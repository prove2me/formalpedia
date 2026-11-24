-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.chartFraction_sub_mem_of_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:28:07.127098+00:00
-- url     : https://prove2.me/submissions/a9543cb8-7708-445f-bb66-5cc43e9ff671

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_BlowupChartCongruence
import Theorems.Thm_FunctorialResolution_Blowup_chartRingHom_coe_eq_chartFraction_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u
variable {R : Type u} [CommRing R]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {A : Type u} [CommRing A] (I : Ideal R) (a : I)
    (φ φ' : HomogeneousLocalization.Away (Blowup.reesGrading I) (Blowup.reesGenerator I a) →+* A)
    (σ σ' : R →+* A) (𝔟 : Ideal A)
    (hφ : ∀ r : R, φ (Blowup.chartRingHom I a r) = σ r)
    (hφ' : ∀ r : R, φ' (Blowup.chartRingHom I a r) = σ' r)
    (hcongr : ∀ r : R, σ r - σ' r ∈ Ideal.span {σ (a : R)} * 𝔟)
    (hnzd : σ (a : R) ∈ nonZeroDivisors A)
    (u : A) (hu : σ' (a : R) = u * σ (a : R)) (b : I) :
    φ (Blowup.chartFraction I a b) - φ' (Blowup.chartFraction I a b) ∈ 𝔟 := by
  obtain ⟨c, hc, hcEq⟩ := Ideal.mem_span_singleton_mul.mp (hcongr (a : R))
  obtain ⟨d, hd, hdEq⟩ := Ideal.mem_span_singleton_mul.mp (hcongr (b : R))
  have hone : (1 : A) - u ∈ 𝔟 := by
    have h1 : σ (a : R) - σ' (a : R) = σ (a : R) * c := hcEq.symm
    rw [hu] at h1
    have h0 : ((1 : A) - u - c) * σ (a : R) = 0 := by linear_combination h1
    have h2 := (mem_nonZeroDivisors_iff.mp hnzd).2 _ h0
    have h3 : (1 : A) - u = c := by linear_combination h2
    rw [h3]
    exact hc
  have hb1 : σ (b : R) = φ (Blowup.chartFraction I a b) * σ (a : R) := by
    rw [← hφ (b : R), ← hφ (a : R), ← map_mul, Blowup.chartRingHom_coe_eq_chartFraction_mul I a b]
  have hb2 : σ' (b : R) = φ' (Blowup.chartFraction I a b) * σ' (a : R) := by
    rw [← hφ' (b : R), ← hφ' (a : R), ← map_mul, Blowup.chartRingHom_coe_eq_chartFraction_mul I a b]
  have h2 : σ (b : R) - σ' (b : R) = σ (a : R) * d := hdEq.symm
  rw [hb1, hb2, hu] at h2
  have h0 : (φ (Blowup.chartFraction I a b) - u * φ' (Blowup.chartFraction I a b) - d) * σ (a : R) = 0 := by
    linear_combination h2
  have h3 := (mem_nonZeroDivisors_iff.mp hnzd).2 _ h0
  have hfin : φ (Blowup.chartFraction I a b) - φ' (Blowup.chartFraction I a b)
      = d - (1 - u) * φ' (Blowup.chartFraction I a b) := by linear_combination h3
  rw [hfin]
  exact 𝔟.sub_mem hd (𝔟.mul_mem_right _ hone)
end FunctorialResolution.EmbeddedResolution
