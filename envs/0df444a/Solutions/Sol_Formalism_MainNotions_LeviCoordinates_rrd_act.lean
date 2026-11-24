-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrd_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:32:43.690831+00:00
-- url     : https://prove2.me/submissions/570163e9-e2d1-43f0-962d-674ec940b76f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrdStronglyMeasurable
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrd_int
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
private theorem integral_comp_mul_left_eq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : G → E) (h : G) :
    ∫ g, f (h * g) ∂μ = ∫ g, f g ∂μ := by
  first
  | exact integral_mul_left_eq_self f h
  | exact integral_comp_mul_left f h
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
    (hmeas : ∀ x y, StronglyMeasurable fun g => ⟪x, π g y⟫_ℂ) {f : G → ℂ} (hf : Integrable f μ) (v : H) (h : G) :
    π h (rrd_vec μ π f v) = ∫ g, f (h⁻¹ * g) • π g v ∂μ := by
  unfold rrd_vec
  rw [← ContinuousLinearMap.integral_comp_comm (π h) (rrd_int hiso hmeas hf v)]
  calc ∫ g, π h (f g • π g v) ∂μ = ∫ g, f (h⁻¹ * (h * g)) • π (h * g) v ∂μ := by
        congr 1
        funext g
        rw [inv_mul_cancel_left, hmul, ContinuousLinearMap.comp_apply, map_smul]
    _ = ∫ g, f (h⁻¹ * g) • π g v ∂μ := integral_comp_mul_left_eq (fun g => f (h⁻¹ * g) • π g v) h
end Formalism.MainNotions.LeviCoordinates
