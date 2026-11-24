-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrd_vec_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:39:29.83295+00:00
-- url     : https://prove2.me/submissions/8bd75311-afd8-4ac6-9d7b-5618cb287194

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrdStronglyMeasurable
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrd_translate
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrd_int
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrd_act
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.MainNotions.LeviCoordinates
open MeasureTheory Filter Topology Set TopologicalSpace
open scoped InnerProductSpace
section Trans
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
private theorem integrable_comp_mul_left' {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
    {E : Type*} [NormedAddCommGroup E] {f : G → E} (hf : Integrable f μ) (h : G) :
    Integrable (fun g => f (h * g)) μ := by
  first
  | exact hf.comp_mul_left h
  | exact hf.comp_mul_left' h
end Trans
section Main
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H]
variable {π : G → (H →L[ℂ] H)}
end Main
end Formalism.MainNotions.LeviCoordinates
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Filter Topology Set TopologicalSpace
open scoped InnerProductSpace
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H]
variable {π : G → (H →L[ℂ] H)}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hiso : ∀ g x, ‖π g x‖ = ‖x‖)
    (hmeas : ∀ x y, StronglyMeasurable fun g => ⟪x, π g y⟫_ℂ) {f : G → ℂ} (hc : Continuous f) (hf : Integrable f μ)
    (v : H) : Tendsto (fun h => π h (rrd_vec μ π f v)) (𝓝 1) (𝓝 (rrd_vec μ π f v)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hT := (rrd_translate (μ := μ) f hc hf).mul_const ‖v‖
  rw [zero_mul] at hT
  refine squeeze_zero (fun h => norm_nonneg _) (fun h => ?_) hT
  rw [rrd_act hmul hiso hmeas hf v h]
  have i1 : Integrable (fun g => f (h⁻¹ * g) • π g v) μ :=
    rrd_int hiso hmeas (integrable_comp_mul_left' hf h⁻¹) v
  have i2 : Integrable (fun g => f g • π g v) μ := rrd_int hiso hmeas hf v
  have i3 : Integrable (fun g => ‖f (h⁻¹ * g) - f g‖ * ‖v‖) μ :=
    ((integrable_comp_mul_left' hf h⁻¹).sub hf).norm.mul_const _
  unfold rrd_vec
  rw [← integral_sub i1 i2, ← integral_mul_const]
  refine norm_integral_le_of_norm_le i3 (Filter.Eventually.of_forall fun g => le_of_eq ?_)
  rw [← sub_smul, norm_smul, hiso]
end Formalism.MainNotions.LeviCoordinates
