-- Prove2me | solution 1 for EisTube.psi_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:58:04.481729+00:00
-- url     : https://prove2.me/submissions/4c5bc023-5155-420f-a0da-f152320217d9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
import Theorems.Thm_EisTube_norm_kern_cz
import Theorems.Thm_EisTube_gauss2
import Theorems.Thm_EisTube_cz_mem_tube
import Theorems.Thm_EisTube_gf_bound
import Theorems.Thm_EisTube_gf_cont

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
theorem _root_.solution [FirstCountableTopology P] {Ω : Set (ι → ℝ)} {h : P → ℝ} (h0 : ∀ p, 0 ≤ h p)
    (hloc : ∀ p, ∃ U ∈ 𝓝 p, BddAbove (h '' U)) {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω))
    (hcont : ∀ z ∈ tube Ω, Continuous (F z))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N)
    {x₀ : ι → ℝ} (h₀ : x₀ ∈ Ω) (t : ι → ℝ) :
    Continuous (fun p => psiAt F x₀ p t) := by
  obtain ⟨C, hC0, hC⟩ := gf_bound h0 hbd (Set.singleton_subset_iff.2 h₀) isCompact_singleton
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨U, hU, B, hB⟩ := hloc p₀
  set E := Real.exp (-(2 * Real.pi * ∑ i, x₀ i * t i))
  refine continuousAt_of_dominated (bound := fun y => (C * B * E) * Real.exp (-(∑ i, y i ^ 2) / 2))
    (Eventually.of_forall fun p => ?_) ?_ (gauss2.const_mul _) (ae_of_all _ fun y => ?_)
  · exact ((gf_cont hhol p h₀).mul (by unfold kern cz; fun_prop)).aestronglyMeasurable
  · filter_upwards [hU] with p hp
    refine ae_of_all _ fun y => ?_
    rw [norm_mul, norm_kern_cz]
    have hBp : h p ≤ B := hB ⟨p, hp, rfl⟩
    calc ‖gf F (cz x₀ y) p‖ * E ≤ (C * h p * Real.exp (-(∑ i, y i ^ 2) / 2)) * E :=
          mul_le_mul_of_nonneg_right (hC x₀ (Set.mem_singleton x₀) y p) (Real.exp_pos _).le
      _ ≤ (C * B * Real.exp (-(∑ i, y i ^ 2) / 2)) * E := by
          gcongr
      _ = _ := by ring
  · have : Continuous (fun p => gf F (cz x₀ y) p) := by
      unfold gf
      exact (hcont _ (cz_mem_tube h₀ y)).mul continuous_const
    exact (this.mul continuous_const).continuousAt
end EisTube
