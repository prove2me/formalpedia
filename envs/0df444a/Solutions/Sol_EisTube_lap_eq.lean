-- Prove2me | solution 1 for EisTube.lap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:34.856792+00:00
-- url     : https://prove2.me/submissions/6cd62692-1fe7-44f0-893d-b70e46866e04

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
import Theorems.Thm_EisTube_kern_cz
import Theorems.Thm_EisTube_exp_cz_split
import Theorems.Thm_EisTube_gauss2
import Theorems.Thm_EisTube_gf_bound
import Theorems.Thm_EisTube_gf_cont
import Theorems.Thm_EisTube_psi_indep
import Theorems.Thm_EisTube_fourierInvCoord
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_fourierInvCoord


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
    {x₀ x : ι → ℝ} (h₀ : x₀ ∈ Ω) (hx : x ∈ Ω) (p : P) (y : ι → ℝ)
    (Lint : ∀ (z : ι → ℂ), Integrable
        (fun t : ι → ℝ => psiAt F x₀ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) :
    (∫ t : ι → ℝ, psiAt F x₀ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, cz x y i * t i)) =
      gf F (cz x y) p := by
  have hgc : Continuous (fun y' => gf F (cz x y') p) := gf_cont hhol p hx
  obtain ⟨C, hC0, hC⟩ := gf_bound h0 hbd (Set.singleton_subset_iff.2 hx) isCompact_singleton
  have hgi : Integrable (fun y' => gf F (cz x y') p) :=
    (gauss2.const_mul (C * h p)).mono' hgc.aestronglyMeasurable
      (ae_of_all _ fun y' => hC x (Set.mem_singleton x) y' p)
  have hhat : ∀ t : ι → ℝ, (∫ y', gf F (cz x y') p *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y' i : ℂ) * t i)) =
      psiAt F x₀ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, (x i : ℂ) * t i) := by
    intro t
    rw [psi_indep hΩo hΩc h0 hhol hbd h₀ hx p t, psiAt]
    simp_rw [kern_cz, ← mul_assoc]
    rw [integral_mul_const]
    conv_rhs => rw [mul_assoc, ← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero, mul_one]
  have hhati : Integrable (fun t : ι → ℝ => ∫ y', gf F (cz x y') p *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y' i : ℂ) * t i)) :=
    (Lint (fun i => (x i : ℂ))).congr (ae_of_all _ fun t => (hhat t).symm)
  have inv := fourierInvCoord ι (fun y' => gf F (cz x y') p) hgc hgi hhati y
  refine (integral_congr_ae (ae_of_all _ fun t => ?_)).trans inv
  rw [hhat t, exp_cz_split]
  ring
end EisTube
