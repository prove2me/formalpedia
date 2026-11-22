-- Prove2me | solution 1 for BornVolume.apexMap_image_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:36.585445+00:00
-- url     : https://prove2.me/submissions/58e271a6-df76-4e95-86a2-0404a3faf198

module
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Theorems.Thm_BornVolume_apexLin_det


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (b : Fin M → ℝ) (hb : 0 ≤ 1 - ∑ k, b k) :
    volume ((fun x => apexLin b x + b) '' openSimplexFree)
      = ENNReal.ofReal (1 - ∑ k, b k) * volume (openSimplexFree (M := M)) := by
  have hregion : (fun x => apexLin b x + b) '' openSimplexFree
      = (fun y => y + b) '' (apexLin b '' openSimplexFree) :=
    (Set.image_image (fun y : Fin M → ℝ => y + b) (⇑(apexLin b)) openSimplexFree).symm
  have htrans : volume ((fun y : Fin M → ℝ => y + b) '' (apexLin b '' openSimplexFree))
      = volume (apexLin b '' openSimplexFree) := by
    rw [show (fun y : Fin M → ℝ => y + b) '' (apexLin b '' openSimplexFree)
          = (fun y => y + (-b)) ⁻¹' (apexLin b '' openSimplexFree) from by
        ext y; simp only [Set.mem_image, Set.mem_preimage]
        exact ⟨by rintro ⟨x, hx, rfl⟩; simpa using hx,
          fun hy => ⟨y + (-b), hy, by abel⟩⟩,
      measure_preimage_add_right]
  rw [hregion, htrans, Measure.addHaar_image_linearMap, apexLin_det, abs_of_nonneg hb]
end BornVolume
