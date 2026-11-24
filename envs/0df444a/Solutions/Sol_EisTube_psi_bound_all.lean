-- Prove2me | solution 1 for EisTube.psi_bound_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:21:13.274435+00:00
-- url     : https://prove2.me/submissions/dc510b03-673f-4156-93ae-0f98581133a8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
import Theorems.Thm_EisTube_psi_bound_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory
open EisTube
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
variable {ι : Type} [Fintype ι]
variable {P : Type*} [TopologicalSpace P]
namespace EisTube
theorem _root_.solution {Ω : Set (ι → ℝ)} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hmid : ∀ x : ι → ℝ, ∃ x₁ ∈ Ω, ∃ x₂ ∈ Ω, x = midpoint ℝ x₁ x₂)
    {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p) {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {x₀ : ι → ℝ} (h₀ : x₀ ∈ Ω) (v : ι → ℝ) :
    ∃ M : ℝ, ∀ p t, ‖psiAt F x₀ p t‖ ≤ M * h p * Real.exp (-(2 * Real.pi * ∑ i, v i * t i)) := by
  obtain ⟨x₁, h₁, x₂, h₂, rfl⟩ := hmid v
  obtain ⟨M₁, hM₁, hb₁⟩ := psi_bound_at hΩo hΩc h0 hhol hbd h₀ h₁
  obtain ⟨M₂, hM₂, hb₂⟩ := psi_bound_at hΩo hΩc h0 hhol hbd h₀ h₂
  refine ⟨max M₁ M₂, fun p t => ?_⟩
  have hm : ∀ i, (midpoint ℝ x₁ x₂) i = (x₁ i + x₂ i) / 2 := fun i => by
    rw [midpoint_eq_smul_add]; simp; ring
  have he : -(2 * Real.pi * ∑ i, (midpoint ℝ x₁ x₂) i * t i) =
      ((-(2 * Real.pi * ∑ i, x₁ i * t i)) + (-(2 * Real.pi * ∑ i, x₂ i * t i))) / 2 := by
    simp only [hm]
    rw [show ∑ i, (x₁ i + x₂ i) / 2 * t i = (∑ i, x₁ i * t i + ∑ i, x₂ i * t i) / 2 by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring]
    ring
  rw [he]
  set a := -(2 * Real.pi * ∑ i, x₁ i * t i)
  set b := -(2 * Real.pi * ∑ i, x₂ i * t i)
  have hM : 0 ≤ max M₁ M₂ := le_max_of_le_left hM₁
  rcases le_total a b with hab | hab
  · calc ‖psiAt F x₀ p t‖ ≤ M₁ * h p * Real.exp a := hb₁ p t
      _ ≤ max M₁ M₂ * h p * Real.exp ((a + b) / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (h0 p))
          (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (mul_nonneg hM (h0 p))
  · calc ‖psiAt F x₀ p t‖ ≤ M₂ * h p * Real.exp b := hb₂ p t
      _ ≤ max M₁ M₂ * h p * Real.exp ((a + b) / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) (h0 p))
          (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le (mul_nonneg hM (h0 p))
end EisTube
