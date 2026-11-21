-- Prove2me | solution 1 for FiniteEnergyPlane.proj_not_mem_range_of_isFastPlane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T00:40:42.889267+00:00
-- url     : https://prove2.me/submissions/50a7ecd5-f489-4822-8194-0b7d79116605

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Theorems.Thm_FiniteEnergyPlane_injective_proj_of_isEmbeddedPlane
import Theorems.Thm_FiniteEnergyPlane_exists_ne_proj_eq_of_proj_mem_range



/-! Hryniewicz (2012) Lemma 6.24 from its two children. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem proj_not_mem_range_of_isFastPlane_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) :
    ∀ z, proj H (u z) ∉ Set.range P.x := by
  intro z₀ hz₀
  obtain ⟨z, w, hne, heq⟩ :=
    exists_ne_proj_eq_of_proj_mem_range H hH J hJ P u hu huP z₀ hz₀
  exact hne (injective_proj_of_isEmbeddedPlane H hH J hJ P u hu huP hue heq)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) :
    ∀ z, proj H (u z) ∉ Set.range P.x :=
  FiniteEnergyPlane.proj_not_mem_range_of_isFastPlane_aux H hH J hJ P u hu huP hue
