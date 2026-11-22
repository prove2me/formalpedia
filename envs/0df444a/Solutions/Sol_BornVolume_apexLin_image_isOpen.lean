-- Prove2me | solution 1 for BornVolume.apexLin_image_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:00.95379+00:00
-- url     : https://prove2.me/submissions/4020d119-6c9e-4c8f-aa15-2ac43d60bd6a

module
public import Definitions.Def_BornVolumeLean_Volume_CellMeasurePos
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
public import Theorems.Thm_BornVolume_isOpen_openSimplexFree


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (b : Fin M → ℝ) (h : LinearMap.det (apexLin b) ≠ 0) :
    IsOpen ((fun x => apexLin b x + b) '' openSimplexFree) := by
  rw [show (fun x => apexLin b x + b) '' openSimplexFree
        = (fun y => y + b) '' (apexLin b '' openSimplexFree) from
      (Set.image_image (fun y : Fin M → ℝ => y + b) (⇑(apexLin b)) openSimplexFree).symm]
  exact (Homeomorph.addRight b).isOpenMap _
    (LinearMap.isOpenMap_of_finiteDimensional _
      (LinearMap.equivOfDetNeZero (apexLin b) h).surjective _ isOpen_openSimplexFree)
end BornVolume
