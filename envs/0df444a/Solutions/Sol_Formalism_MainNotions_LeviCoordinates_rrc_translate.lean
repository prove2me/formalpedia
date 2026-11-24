-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrc_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:06:49.5838+00:00
-- url     : https://prove2.me/submissions/ad0333f0-bf0b-4a87-8f1c-21e3e67765ae

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrcTendstoVec
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_inner

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
omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [CompleteSpace H]
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    {k : Set G} {v w : H} (hw : ∀ u, ⟪w, u⟫_ℂ = ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ) (h : G) (u : H) :
    ⟪π h w, u⟫_ℂ = ∫ g in h • k, ⟪π g v, u⟫_ℂ ∂μ := by
  have e1 : π h (π h⁻¹ u) = u := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul, mul_inv_cancel, hone]; rfl
  have e2 : ∀ g, ⟪π g v, π h⁻¹ u⟫_ℂ = ⟪π (h * g) v, u⟫_ℂ := fun g => by
    rw [← rrc_inner hn h, e1, hmul]; rfl
  have e3 : (fun g => h * g) ⁻¹' (h • k) = k := by
    ext g; simp [Set.mem_smul_set_iff_inv_smul_mem]
  have e4 := (measurePreserving_mul_left μ h).setIntegral_preimage_emb (measurableEmbedding_mulLeft h)
    (fun g => ⟪π g v, u⟫_ℂ) (h • k)
  rw [e3] at e4
  calc ⟪π h w, u⟫_ℂ = ⟪π h w, π h (π h⁻¹ u)⟫_ℂ := by rw [e1]
    _ = ⟪w, π h⁻¹ u⟫_ℂ := rrc_inner hn h _ _
    _ = ∫ g in k, ⟪π g v, π h⁻¹ u⟫_ℂ ∂μ := hw _
    _ = ∫ g in k, ⟪π (h * g) v, u⟫_ℂ ∂μ := by simp only [e2]
    _ = ∫ g in h • k, ⟪π g v, u⟫_ℂ ∂μ := e4
end Formalism.MainNotions.LeviCoordinates
