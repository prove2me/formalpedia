-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrd_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:41:36.511116+00:00
-- url     : https://prove2.me/submissions/d791c00a-1e01-47b6-89a7-72afae046ecb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrdStronglyMeasurable
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
private theorem integral_comp_mul_left_eq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (f : G → E) (h : G) :
    ∫ g, f (h * g) ∂μ = ∫ g, f g ∂μ := by
  first
  | exact integral_mul_left_eq_self f h
  | exact integral_comp_mul_left f h
private theorem abs_norm_sub_sub_norm_add_norm_le_two_mul (a b : ℂ) : |‖a - b‖ - ‖a‖ + ‖b‖| ≤ 2 * ‖b‖ := by
  have h1 := norm_sub_le a b
  have h2 : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    calc ‖a‖ = ‖(a - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le _ _
  rw [abs_le]
  constructor <;> linarith [norm_nonneg b, norm_nonneg a, norm_nonneg (a - b)]
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
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (f : G → ℂ) (hc : Continuous f) (hf : Integrable f μ) :
    Tendsto (fun h : G => ∫ g, ‖f (h⁻¹ * g) - f g‖ ∂μ) (𝓝 1) (𝓝 0) := by
  have key : ∀ h : G, ∫ g, ‖f (h⁻¹ * g) - f g‖ ∂μ =
      ∫ g, (‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖ + ‖f g‖) ∂μ := by
    intro h
    have i1 : Integrable (fun g => f (h⁻¹ * g)) μ := integrable_comp_mul_left' hf h⁻¹
    have i2 : Integrable (fun g => ‖f (h⁻¹ * g) - f g‖) μ := (i1.sub hf).norm
    have e : ∫ g, ‖f (h⁻¹ * g)‖ ∂μ = ∫ g, ‖f g‖ ∂μ := integral_comp_mul_left_eq (fun g => ‖f g‖) h⁻¹
    have i3 : Integrable (fun g => ‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖) μ := i2.sub i1.norm
    rw [integral_add i3 hf.norm, integral_sub i2 i1.norm, e]
    ring
  have hfun : (fun h : G => ∫ g, ‖f (h⁻¹ * g) - f g‖ ∂μ) =
      fun h => ∫ g, (‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖ + ‖f g‖) ∂μ := funext key
  rw [hfun]
  have hmeas : ∀ᶠ h in 𝓝 (1 : G),
      AEStronglyMeasurable (fun g => ‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖ + ‖f g‖) μ :=
    Filter.Eventually.of_forall fun h =>
      (by fun_prop : Continuous fun g => ‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖ + ‖f g‖).aestronglyMeasurable
  have hbound : ∀ᶠ h in 𝓝 (1 : G), ∀ᵐ g ∂μ, ‖‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖ + ‖f g‖‖ ≤ 2 * ‖f g‖ :=
    Filter.Eventually.of_forall fun h => Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs]
      exact abs_norm_sub_sub_norm_add_norm_le_two_mul _ _
  have hlim : ∀ᵐ g ∂μ, Tendsto (fun h : G => ‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖ + ‖f g‖) (𝓝 1) (𝓝 0) :=
    Filter.Eventually.of_forall fun g => by
      have hcont : Continuous fun h : G => ‖f (h⁻¹ * g) - f g‖ - ‖f (h⁻¹ * g)‖ + ‖f g‖ := by fun_prop
      simpa using hcont.tendsto 1
  have := tendsto_integral_filter_of_dominated_convergence (fun g => 2 * ‖f g‖) hmeas hbound
    (hf.norm.const_mul 2) hlim
  simpa using this
end Formalism.MainNotions.LeviCoordinates
