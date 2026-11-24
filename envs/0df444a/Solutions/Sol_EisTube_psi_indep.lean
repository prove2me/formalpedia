-- Prove2me | solution 1 for EisTube.psi_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:58:10.729894+00:00
-- url     : https://prove2.me/submissions/52172278-517a-4e38-b899-5c2b0fa68a53

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
import Theorems.Thm_EisTube_norm_kern_cz
import Theorems.Thm_EisTube_gf_bound
import Theorems.Thm_EisTube_gf_diff
import Theorems.Thm_EisTube_tubeShift
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_tubeShift


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
    {x₁ x₂ : ι → ℝ} (h₁ : x₁ ∈ Ω) (h₂ : x₂ ∈ Ω) (p : P) (t : ι → ℝ) :
    psiAt F x₁ p t = psiAt F x₂ p t := by
  refine tubeShift ι Ω hΩo hΩc (fun z => gf F z p * kern z t) (gf_diff hhol p t) ?_ x₁ h₁ x₂ h₂
  intro K hK hKc
  obtain ⟨C, hC0, hC⟩ := gf_bound h0 hbd hK hKc
  obtain ⟨Q, hQ⟩ : BddAbove ((fun x : ι → ℝ => Real.exp (-(2 * Real.pi * ∑ i, x i * t i))) '' K) :=
    hKc.bddAbove_image (by fun_prop)
  refine ⟨C * h p * Q, fun x hx y => ?_⟩
  show ‖gf F (cz x y) p * kern (cz x y) t‖ ≤ _
  rw [norm_mul, norm_kern_cz]
  have hq : Real.exp (-(2 * Real.pi * ∑ i, x i * t i)) ≤ Q := hQ ⟨x, hx, rfl⟩
  calc ‖gf F (cz x y) p‖ * Real.exp (-(2 * Real.pi * ∑ i, x i * t i))
      ≤ (C * h p * Real.exp (-(∑ i, y i ^ 2) / 2)) * Q :=
        mul_le_mul (hC x hx y p) hq (Real.exp_pos _).le
          (mul_nonneg (mul_nonneg hC0 (h0 p)) (Real.exp_pos _).le)
    _ = C * h p * Q * Real.exp (-(∑ i, y i ^ 2) / 2) := by ring
end EisTube
