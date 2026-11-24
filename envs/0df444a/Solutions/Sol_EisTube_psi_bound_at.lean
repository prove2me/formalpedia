-- Prove2me | solution 1 for EisTube.psi_bound_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:35.654864+00:00
-- url     : https://prove2.me/submissions/200ed9f3-b8d7-4f0a-94a1-e609c9c71858

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
import Theorems.Thm_EisTube_norm_kern_cz
import Theorems.Thm_EisTube_gauss2
import Theorems.Thm_EisTube_gf_bound
import Theorems.Thm_EisTube_psi_indep

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
    {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p) {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {x₀ x : ι → ℝ} (h₀ : x₀ ∈ Ω) (hx : x ∈ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p t, ‖psiAt F x₀ p t‖ ≤ M * h p * Real.exp (-(2 * Real.pi * ∑ i, x i * t i)) := by
  obtain ⟨C, hC0, hC⟩ := gf_bound h0 hbd (Set.singleton_subset_iff.2 hx) isCompact_singleton
  have hI2 : 0 ≤ ∫ y : ι → ℝ, Real.exp (-(∑ i, y i ^ 2) / 2) :=
    integral_nonneg fun y => (Real.exp_pos _).le
  refine ⟨C * ∫ y : ι → ℝ, Real.exp (-(∑ i, y i ^ 2) / 2), mul_nonneg hC0 hI2, fun p t => ?_⟩
  rw [psi_indep hΩo hΩc h0 hhol hbd h₀ hx p t]
  have hb : ∀ y : ι → ℝ, ‖gf F (cz x y) p * kern (cz x y) t‖ ≤
      (C * h p * Real.exp (-(2 * Real.pi * ∑ i, x i * t i))) * Real.exp (-(∑ i, y i ^ 2) / 2) :=
    fun y => by
      rw [norm_mul, norm_kern_cz]
      have := hC x (Set.mem_singleton x) y p
      calc ‖gf F (cz x y) p‖ * Real.exp (-(2 * Real.pi * ∑ i, x i * t i))
          ≤ (C * h p * Real.exp (-(∑ i, y i ^ 2) / 2)) * Real.exp (-(2 * Real.pi * ∑ i, x i * t i)) :=
            mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
        _ = _ := by ring
  have hn := norm_integral_le_of_norm_le (gauss2.const_mul
    (C * h p * Real.exp (-(2 * Real.pi * ∑ i, x i * t i)))) (ae_of_all _ hb)
  rw [integral_const_mul] at hn
  refine hn.trans (le_of_eq ?_)
  ring
end EisTube
