-- Prove2me | solution 1 for EisTube.tubeExtends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:32:56.511492+00:00
-- url     : https://prove2.me/submissions/125bfbdb-9f93-450c-994b-6fe008348011

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
import Theorems.Thm_EisTube_cz_re_im
import Theorems.Thm_EisTube_psi_bound_all
import Theorems.Thm_EisTube_psi_meas
import Theorems.Thm_EisTube_psi_cont
import Theorems.Thm_EisTube_lap_eq
import Theorems.Thm_EisTube_laplaceEntire
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_laplaceEntire


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
namespace EisTube
theorem _root_.solution (P : Type*) [TopologicalSpace P] [FirstCountableTopology P] :
    TubeExtends (ι := ι) P := by
  intro Ω hΩo hΩc hmid h h0 hloc F hhol hcont hbd
  obtain ⟨x₀, h₀, -, -, -⟩ := hmid 0
  obtain ⟨Lint, Ldiff, Lcont, Lbd⟩ := laplaceEntire ι P h h0 hloc (psiAt F x₀)
    (psi_meas hhol h₀) (psi_cont h0 hloc hhol hcont hbd h₀)
    (psi_bound_all hΩo hΩc hmid h0 hhol hbd h₀)
  refine ⟨fun z p => (∫ t : ι → ℝ, psiAt F x₀ p t *
      Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i)) * Complex.exp (-∑ i, z i ^ 2),
    fun p => (Ldiff p).mul (by fun_prop), ?_, ?_, ?_⟩
  · intro z hz p
    have hx : reV z ∈ Ω := hz
    beta_reduce
    rw [← cz_re_im z, lap_eq hΩo hΩc h0 hhol hbd h₀ hx p (imV z) (Lint p), gf, mul_assoc,
      ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  · exact Lcont.mul (by fun_prop)
  · intro K hK
    obtain ⟨C, hC⟩ := Lbd K hK
    obtain ⟨Q, hQ⟩ : BddAbove ((fun z : ι → ℂ => ‖Complex.exp (-∑ i, z i ^ 2)‖) '' K) :=
      hK.bddAbove_image (by fun_prop)
    refine ⟨C * Q, fun z hz p => ?_⟩
    rw [norm_mul]
    have h1 := hC z hz p
    have h2 : ‖Complex.exp (-∑ i, z i ^ 2)‖ ≤ Q := hQ ⟨z, hz, rfl⟩
    calc _ ≤ (C * h p) * Q := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = C * Q * h p := by ring
end EisTube
