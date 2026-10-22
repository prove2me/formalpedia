-- Prove2me | solution 1 for DRConvexOpt.Lifting.cone_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:35:56.591195+00:00
-- url     : https://prove2.me/submissions/e50e2044-9f2e-406f-89d8-0f41b3ba5a76

import Mathlib
import Definitions.Def_DRConvexOpt_Lifting_Setting

set_option autoImplicit false
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {nM : ℕ} (K : Set (Fin nM → ℝ)) (hK : DRConvexOpt.Reform.IsProperCone K)
    (φ ψ : Ω → (Fin nM → ℝ)) (hφ : Integrable φ μ) (hψ : Integrable ψ μ)
    (h : ∀ᵐ ω ∂μ, ψ ω - φ ω ∈ K) :
    ∫ ω, ψ ω ∂μ - ∫ ω, φ ω ∂μ ∈ K := by
  obtain ⟨hcl, h0, hadd, hsmul, -, -⟩ := hK
  have hconv : Convex ℝ K := by
    intro x hx y hy a b ha hb _
    exact hadd _ (hsmul x hx a ha) _ (hsmul y hy b hb)
  have := hconv.integral_mem hcl h (hψ.sub hφ)
  rwa [integral_sub hψ hφ] at this
