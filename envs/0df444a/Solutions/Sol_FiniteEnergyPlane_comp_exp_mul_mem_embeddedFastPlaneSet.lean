-- Prove2me | solution 1 for FiniteEnergyPlane.comp_exp_mul_mem_embeddedFastPlaneSet
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-23T22:33:24.224167+00:00
-- url     : https://prove2.me/submissions/3d33d2d7-c697-4b14-bc4c-58d74f52d533

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_isPrime_of_isFastPlane_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_piDs_ne_zero_iff_dlambdaDensity_pos
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_comp_mul
import Theorems.Thm_FiniteEnergyPlane_dlambdaDensity_comp_mul
import Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_comp_mul
import Theorems.Thm_FiniteEnergyPlane_isNondegenerateEnd_comp_exp_mul



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem comp_exp_mul_mem_embeddedFastPlaneSet_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (K : Set (V 1)) (γ : ℝ) (u : ℂ → V 1) (hu : u ∈ embeddedFastPlaneSet H J P K γ) (α : ℝ) :
    (fun z => u (Complex.exp (((2 * π * α : ℝ) : ℂ) * Complex.I) * z)) ∈
      embeddedFastPlaneSet H J P K γ := by
  obtain ⟨⟨hu, huP, hu0, huE⟩, hue⟩ := hu
  have hEnd := isNondegenerateEnd_comp_exp_mul H u P huP α
  have hn : ‖Complex.exp (((2 * π * α : ℝ) : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  generalize Complex.exp (((2 * π * α : ℝ) : ℂ) * Complex.I) = A at hEnd hn ⊢
  have hA : A ≠ 0 := by rintro rfl; simp at hn
  have hfe := hu.1
  have hs : ContDiff ℝ ∞ u := contDiffOn_univ.1 hfe.1
  have hp : Differentiable ℝ (fun z => proj H (u z)) := fun z =>
    ((contDiffAt_aCoord_proj H hH (u z) (hfe.2.1 z trivial)).2.comp z
      hs.contDiffAt).differentiableAt (by simp)
  have hFE := isFiniteEnergyCurve_comp_mul H hH J hJ u hfe A hA
  have hpi : ∀ z, piDs H (fun z => u (A * z)) z ≠ 0 := by
    intro z
    refine (piDs_ne_zero_iff_dlambdaDensity_pos H hH J hJ Set.univ isOpen_univ _
      (fun z _ => hFE.2.1 z trivial) hFE.2.2.1 (Set.mem_univ z)).2 ?_
    have h0 : 0 < dlambdaDensity H u (A * z) :=
      (piDs_ne_zero_iff_dlambdaDensity_pos H hH J hJ Set.univ isOpen_univ u
        (fun z _ => hfe.2.1 z trivial) hfe.2.2.1 (Set.mem_univ _)).1
        (piDs_ne_zero_of_isFastPlane H hH J hJ u hu _)
    rw [dlambdaDensity_comp_mul H u A z (hp _)]
    exact mul_pos (Complex.normSq_pos.2 hA) h0
  refine ⟨⟨⟨hFE, ⟨P, isPrime_of_isFastPlane_of_isNondegenerateEnd H hH J hJ u hu P huP, hEnd⟩,
    ∅, fun z => ?_, fun _ => 0, ?_, ?_⟩, hEnd, ?_, ?_⟩, ?_, ?_⟩
  · exact iff_of_false (by simp) (fun h => hpi z h.2)
  · simp
  · simp
  · simpa using hu0
  · rw [dlambdaEnergy_comp_mul H u A hA hp _ (measurableSet_lt measurable_const measurable_norm),
      ← huE]
    congr 1
    ext w
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rwa [norm_mul, hn, one_mul]
    · intro hw
      refine ⟨w / A, ?_, by field_simp⟩
      rwa [norm_div, hn, div_one]
  · intro z w h
    exact mul_left_cancel₀ hA (hue.1 h)
  · intro z v w h
    have hd : HasFDerivAt (fun y : ℂ => A * y) (A • ContinuousLinearMap.id ℝ ℂ) z :=
      (hasFDerivAt_id z).const_smul A
    have h2 : HasFDerivAt (fun z => u (A * z)) _ z :=
      ((hs.differentiable (by simp) (A * z)).hasFDerivAt).comp z hd
    rw [h2.fderiv] at h
    exact mul_left_cancel₀ hA (hue.2 _ h)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (K : Set (V 1)) (γ : ℝ) (u : ℂ → V 1) (hu : u ∈ embeddedFastPlaneSet H J P K γ) (α : ℝ) :
    (fun z => u (Complex.exp (((2 * π * α : ℝ) : ℂ) * Complex.I) * z)) ∈
      embeddedFastPlaneSet H J P K γ :=
  comp_exp_mul_mem_embeddedFastPlaneSet_aux H hH J hJ P K γ u hu α
