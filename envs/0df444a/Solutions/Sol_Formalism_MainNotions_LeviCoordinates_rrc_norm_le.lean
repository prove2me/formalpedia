-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrc_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:29:54.512288+00:00
-- url     : https://prove2.me/submissions/16b054ae-ec5f-4451-afcb-94216131dd26

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrcTendstoVec
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_bound
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_intOn
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_translate

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
omit [LocallyCompactSpace G] [SecondCountableTopology G] [CompleteSpace H]
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ)
    {k : Set G} (hk : IsCompact k) {v w : H} (hw : ∀ u, ⟪w, u⟫_ℂ = ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ) (h : G) :
    ‖π h w - w‖ ≤ ‖v‖ * (μ.real (h • k \ k) + μ.real (k \ h • k)) := by
  have hkm : MeasurableSet k := hk.measurableSet
  have hk' : IsCompact (h • k) := hk.smul h
  have hkm' : MeasurableSet (h • k) := hk'.measurableSet
  have key : ∀ u, ‖⟪π h w - w, u⟫_ℂ‖ ≤ ‖v‖ * ‖u‖ * (μ.real (h • k \ k) + μ.real (k \ h • k)) := by
    intro u
    rw [inner_sub_left, rrc_translate hmul hone hn hw h u, hw u]
    have a1 := integral_inter_add_sdiff (f := fun g => ⟪π g v, u⟫_ℂ) hkm (rrc_intOn hn hm hk'.measure_lt_top v u)
    have a2 := integral_inter_add_sdiff (f := fun g => ⟪π g v, u⟫_ℂ) hkm' (rrc_intOn hn hm hk.measure_lt_top v u)
    rw [inter_comm] at a2
    rw [← a1, ← a2, add_sub_add_left_eq_sub]
    have b1 := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := h • k \ k)
      (lt_of_le_of_lt (measure_mono sdiff_subset) hk'.measure_lt_top) (fun g _ => rrc_bound hn g v u)
    have b2 := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := k \ h • k)
      (lt_of_le_of_lt (measure_mono sdiff_subset) hk.measure_lt_top) (fun g _ => rrc_bound hn g v u)
    calc _ ≤ ‖∫ g in h • k \ k, ⟪π g v, u⟫_ℂ ∂μ‖ + ‖∫ g in k \ h • k, ⟪π g v, u⟫_ℂ ∂μ‖ := norm_sub_le _ _
      _ ≤ ‖v‖ * ‖u‖ * μ.real (h • k \ k) + ‖v‖ * ‖u‖ * μ.real (k \ h • k) := add_le_add b1 b2
      _ = _ := by ring
  have h2 := key (π h w - w)
  rw [inner_self_eq_norm_sq_to_K] at h2
  have h3 : ‖((‖π h w - w‖ : ℝ) : ℂ) ^ 2‖ = ‖π h w - w‖ ^ 2 := by
    rw [norm_pow, Complex.norm_real, norm_norm]
  have h2' : ‖π h w - w‖ ^ 2 ≤ ‖v‖ * ‖π h w - w‖ * (μ.real (h • k \ k) + μ.real (k \ h • k)) := by
    rw [← h3]; exact h2
  by_cases h0 : ‖π h w - w‖ = 0
  · rw [h0]; positivity
  · have hpos : 0 < ‖π h w - w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have : ‖π h w - w‖ * ‖π h w - w‖ ≤ ‖π h w - w‖ * (‖v‖ * (μ.real (h • k \ k) + μ.real (k \ h • k))) := by
      calc _ = ‖π h w - w‖ ^ 2 := by ring
        _ ≤ _ := h2'
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hpos
end Formalism.MainNotions.LeviCoordinates
