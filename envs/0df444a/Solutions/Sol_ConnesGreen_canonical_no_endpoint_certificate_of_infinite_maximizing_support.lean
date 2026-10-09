-- Prove2me | solution 1 for ConnesGreen.canonical_no_endpoint_certificate_of_infinite_maximizing_support
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T06:55:18.18527+00:00
-- url     : https://prove2.me/submissions/c088d8d3-278f-456c-a799-b52572be242a

import Definitions.Def_ConnesGreen_positive_endpoint_support
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

import Theorems.Thm_ConnesGreen_canonical_endpoint_certificate_iff_pointwise_finite_support
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ConnesGreen WeilDefect WeilDefect.ConnesNative ContinuousFunctionalCalculus WeilDefect.MarkerStability
namespace ConnesGreen
end ConnesGreen
theorem solution
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (hμ : 0 < canonicalCertificateThreshold t ht S) (x : Physical t)
    (hx : x ∈ canonicalMaximizingSpace t ht S)
    (hinfinite : ∀ F : Finset CriticalZeros, ∃ ρ : CriticalZeros, ρ ∉ F ∧
      ⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ ≠ 0) :
    ∀ F : Finset CriticalZeros,
      ¬ 0 ≤ canonicalFiniteSelectedCorrection t ht S F (canonicalCertificateThreshold t ht S) := by
  intro F hF
  obtain ⟨F₀, hf⟩ := (ConnesGreen.canonical_endpoint_certificate_iff_pointwise_finite_support
    t ht S hμ).mp ⟨F, hF⟩ x hx
  obtain ⟨ρ, hρ, hn⟩ := hinfinite F₀
  exact hn (hf ρ hρ)

