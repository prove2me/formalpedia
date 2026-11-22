-- Prove2me | solution 1 for BornVolume.apexMap_image_subset_of_closedSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:11.180714+00:00
-- url     : https://prove2.me/submissions/1751aa24-0e73-46cc-b450-a463a0ff4e5e

module
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Theorems.Thm_BornVolume_apexLin_apply


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (b : Fin M → ℝ)
    (hb0 : ∀ k, 0 ≤ b k) (hbsum : ∑ k, b k < 1) :
    (fun x => apexLin b x + b) '' openSimplexFree ⊆ openSimplexFree := by
  rintro _ ⟨t, ⟨htpos, htsum⟩, rfl⟩
  have happ : ∀ k, (apexLin b t + b) k = t k + (1 - ∑ j, t j) * b k := by
    intro k; rw [Pi.add_apply, apexLin_apply]; ring
  refine ⟨fun k => ?_, ?_⟩
  · show (0 : ℝ) < (apexLin b t + b) k
    rw [happ]
    have hbk := mul_nonneg (le_of_lt (sub_pos.mpr htsum)) (hb0 k)
    linarith [htpos k]
  · show ∑ k, (apexLin b t + b) k < 1
    simp_rw [happ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith [mul_pos (sub_pos.mpr htsum) (sub_pos.mpr hbsum)]
end BornVolume
