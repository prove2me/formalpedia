-- Prove2me | solution 1 for ConnesGreen.canonical_endpoint_certificate_iff_pointwise_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T06:41:43.55036+00:00
-- url     : https://prove2.me/submissions/89966b4d-b9dd-42ee-ab87-694071fe16e7

import Definitions.Def_ConnesGreen_positive_endpoint_support
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

import Theorems.Thm_ConnesGreen_canonicalPositiveCovariance_compact
import Theorems.Thm_ConnesGreen_canonical_endpoint_certificate_of_maximizing_capture
import Theorems.Thm_ConnesGreen_canonical_finite_certificate_neutral_tail_zero
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ConnesGreen WeilDefect WeilDefect.ConnesNative ContinuousFunctionalCalculus WeilDefect.MarkerStability
namespace ConnesGreen
private theorem finite_coefficients (F : Finset CriticalZeros) :
    FiniteDimensional ℂ (ℓ²({ρ : CriticalZeros // ρ ∈ F}, ℂ)) := by
  let L : ℓ²({ρ : CriticalZeros // ρ ∈ F}, ℂ) →ₗ[ℂ]
      ({ρ : CriticalZeros // ρ ∈ F} → ℂ) :=
    { toFun := fun f ρ => f ρ
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply FiniteDimensional.of_injective L
  intro f g h
  apply lp.ext
  exact h
theorem canonicalLossCovariance_compact (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) : IsCompactOperator (canonicalLossCovariance t ht S) := by
  letI : FiniteDimensional ℂ (ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) := finite_coefficients S
  exact ((isCompactOperator_of_locallyCompactSpace_rng
    (canonicalSelectedSynthesis t ht S)).comp_clm
      (canonicalSelectedSynthesis t ht S).adjoint).sub
    (canonicalPositiveCovariance_compact t ht)
theorem canonical_positive_threshold_eigenspace_finite (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (hμ : 0 < canonicalCertificateThreshold t ht S) :
    FiniteDimensional ℂ (Module.End.eigenspace (canonicalLossCovariance t ht S).toLinearMap
      (canonicalCertificateThreshold t ht S : ℂ)) := by
  exact ContinuousLinearMap.finite_dimensional_eigenspace (canonicalLossCovariance_compact t ht S) _
    (Complex.ofReal_ne_zero.mpr hμ.ne')
theorem canonical_mem_maximizingSpace_iff (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (x : Physical t) :
    x ∈ canonicalMaximizingSpace t ht S ↔
      canonicalLossCovariance t ht S x = (canonicalCertificateThreshold t ht S : ℂ) • x :=
  Module.End.mem_eigenspace_iff
theorem canonicalLossCovariance_quadratic (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (x : Physical t) :
    RCLike.re ⟪canonicalLossCovariance t ht S x, x⟫_ℂ =
      ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 -
        ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 := by
  have hn := (canonicalSelectedSynthesis t ht S).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  have hp := (canonicalPositiveSynthesis t ht).adjoint.apply_norm_sq_eq_inner_adjoint_left x
  simp only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply] at hn hp
  simp only [canonicalLossCovariance, canonicalPositiveCovariance,
    ContinuousLinearMap.sub_apply, inner_sub_left, map_sub, ContinuousLinearMap.comp_apply]
  rw [← hn, ← hp]
theorem canonical_maximizing_margin_zero (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (x : Physical t)
    (hx : x ∈ canonicalMaximizingSpace t ht S) : canonicalSharpMargin t ht S x = 0 := by
  have hq := canonicalLossCovariance_quadratic t ht S x
  have he := (canonical_mem_maximizingSpace_iff t ht S x).mp hx
  have hscalar : RCLike.re ⟪(canonicalCertificateThreshold t ht S : ℂ) • x, x⟫_ℂ =
      canonicalCertificateThreshold t ht S * ‖x‖ ^ 2 := by
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  rw [he, hscalar] at hq
  unfold canonicalSharpMargin
  linarith
theorem canonical_endpoint_certificate_maximizing_custody
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros)
    (hμ : 0 < canonicalCertificateThreshold t ht S)
    (hF : 0 ≤ canonicalFiniteSelectedCorrection t ht S F (canonicalCertificateThreshold t ht S)) :
    ∀ x : Physical t, x ∈ canonicalMaximizingSpace t ht S →
      ∀ ρ : CriticalZeros, ρ ∉ F →
        ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0 := by
  intro x hx
  exact canonical_finite_certificate_neutral_tail_zero t ht S F _ hμ hF x
    (canonical_maximizing_margin_zero t ht S x hx)
theorem canonical_maximizing_capture_of_pointwise_finite_support
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (hμ : 0 < canonicalCertificateThreshold t ht S)
    (hpoint : ∀ x : Physical t, x ∈ canonicalMaximizingSpace t ht S →
      ∃ F : Finset CriticalZeros, ∀ ρ : CriticalZeros, ρ ∉ F →
        ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) :
    ∃ F : Finset CriticalZeros, ∀ x : Physical t, x ∈ canonicalMaximizingSpace t ht S →
      ∀ ρ : CriticalZeros, ρ ∉ F →
        ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0 := by
  let E := canonicalMaximizingSpace t ht S
  letI : FiniteDimensional ℂ E := canonical_positive_threshold_eigenspace_finite t ht S hμ
  let b := Module.finBasis ℂ E
  choose f hf using (fun i => hpoint (b i) (b i).2)
  refine ⟨Finset.univ.biUnion f, ?_⟩
  intro x hx ρ hρ
  have hn (i) : ρ ∉ f i := by
    intro hi
    exact hρ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩)
  let y : E := ⟨x, hx⟩
  have he := congrArg Subtype.val (b.sum_repr y)
  have he' : (∑ i, b.repr y i • (b i : Physical t)) = x := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using he
  rw [← he', inner_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [inner_smul_right, hf i ρ (hn i), mul_zero]
end ConnesGreen
theorem solution
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (hμ : 0 < canonicalCertificateThreshold t ht S) :
    (∃ F : Finset CriticalZeros,
      0 ≤ canonicalFiniteSelectedCorrection t ht S F (canonicalCertificateThreshold t ht S)) ↔
    (∀ x : Physical t, x ∈ canonicalMaximizingSpace t ht S →
      ∃ F : Finset CriticalZeros, ∀ ρ : CriticalZeros, ρ ∉ F →
        ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ = 0) := by
  constructor
  · rintro ⟨F, hF⟩ x hx
    exact ⟨F, canonical_endpoint_certificate_maximizing_custody t ht S F hμ hF x hx⟩
  · intro hp
    obtain ⟨F₀, hcapture⟩ := canonical_maximizing_capture_of_pointwise_finite_support t ht S hμ hp
    obtain ⟨F, _, _, _, _, hF⟩ := canonical_endpoint_certificate_of_maximizing_capture
      t ht S F₀ hμ hcapture 1 zero_lt_one
    exact ⟨F, hF⟩
