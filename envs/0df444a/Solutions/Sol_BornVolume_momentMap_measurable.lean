-- Prove2me | solution 1 for BornVolume.momentMap_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:59:09.634203+00:00
-- url     : https://prove2.me/submissions/b5676194-550e-4705-85b4-1784d8c5285b

module
public import Definitions.Def_BornVolumeLean_Volume_MomentMap
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_BornVolumeLean_Volume_MomentMeasurable
public import Theorems.Thm_P2M_Projectivization_measurable_iff_measurable_comp_mk__5d5b7c48e6fb
public import Theorems.Thm_Projectivization_momentMap_mk


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
open BornVolume
variable {N : ℕ}
namespace BornVolume
theorem _root_.solution (i : Fin N) :
    Measurable (fun p : CPN N => momentMap p i) := by
  borelize (EuclideanSpace ℂ (Fin N))
  rw [Projectivization.measurable_iff_measurable_comp_mk']
  have hcomp : (fun p : CPN N => momentMap p i) ∘ (Projectivization.mk' ℂ)
      = fun w : { v : EuclideanSpace ℂ (Fin N) // v ≠ 0 } =>
          ‖(w : EuclideanSpace ℂ (Fin N)) i‖ ^ 2 / ‖(w : EuclideanSpace ℂ (Fin N))‖ ^ 2 := by
    funext w
    show momentMap (Projectivization.mk ℂ (w : EuclideanSpace ℂ (Fin N)) w.2) i = _
    rw [momentMap_mk]
  rw [hcomp]
  have hden : ∀ w : { v : EuclideanSpace ℂ (Fin N) // v ≠ 0 },
      ‖(w : EuclideanSpace ℂ (Fin N))‖ ^ 2 ≠ 0 :=
    fun w => pow_ne_zero 2 (norm_ne_zero_iff.mpr w.2)
  refine Measurable.div ?_ ?_
  · exact ((((EuclideanSpace.proj i).continuous).comp continuous_subtype_val).norm.pow 2).measurable
  · exact ((continuous_subtype_val.norm).pow 2).measurable
end BornVolume
