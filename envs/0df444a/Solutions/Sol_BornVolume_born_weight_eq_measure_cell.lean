-- Prove2me | solution 1 for BornVolume.born_weight_eq_measure_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:47.852895+00:00
-- url     : https://prove2.me/submissions/2f8f714a-39d8-4a4a-93ad-d57a20d7d32c

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Theorems.Thm_BornVolume_freeMoment_eq_ratioN
public import Theorems.Thm_BornVolume_ratioN_momentMap_mk
public import Theorems.Thm_BornVolume_fsMeasure_preimage_cell
public import Theorems.Thm_Matrix_UnitaryGroup_fsMeasure_unique


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (μ : Measure (CPN (M + 1))) [IsProbabilityMeasure μ]
    (hμ : ∀ U : Matrix.unitaryGroup (Fin (M + 1)) ℂ, Measure.map (fun p => U • p) μ = μ)
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1) (i : Fin M) :
    μ ((fun (p : CPN (M + 1)) (k : Fin M) => momentMap p (Fin.castSucc k)) ⁻¹'
        (replaceMap (fun k => ‖ψ (Fin.castSucc k)‖ ^ 2) i '' openSimplexFree))
      = ENNReal.ofReal (‖ψ (Fin.castSucc i)‖ ^ 2) := by
  have : NeZero (M + 1) := ⟨Nat.succ_ne_zero M⟩
  have hψ0 : ψ ≠ 0 := by rintro rfl; simp at hψ
  obtain ⟨p₀⟩ := (inferInstance : Nonempty (CPN (M + 1)))
  rw [fsMeasure_unique p₀ μ hμ, freeMoment_eq_ratioN, ← ratioN_momentMap_mk ψ hψ0 hψ,
    fsMeasure_preimage_cell p₀ ψ hψ0 hψ i, EuclideanSpace.inner_single_left, map_one,
    one_mul]
end BornVolume
