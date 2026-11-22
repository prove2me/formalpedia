-- Prove2me | solution 1 for BornVolume.born_weight_eq_measure_apexCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:48.874518+00:00
-- url     : https://prove2.me/submissions/8ce71e33-3afe-4a79-8d43-8e41d0fe7d8d

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Theorems.Thm_BornVolume_freeMoment_eq_ratioN
public import Theorems.Thm_BornVolume_ratioN_momentMap_mk
public import Theorems.Thm_BornVolume_fsMeasure_preimage_apexCell
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
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ : ‖ψ‖ = 1) :
    μ ((fun (p : CPN (M + 1)) (k : Fin M) => momentMap p (Fin.castSucc k)) ⁻¹'
        ((fun x => apexLin (fun k => ‖ψ (Fin.castSucc k)‖ ^ 2) x
          + fun k => ‖ψ (Fin.castSucc k)‖ ^ 2) '' openSimplexFree))
      = ENNReal.ofReal (‖ψ (Fin.last M)‖ ^ 2) := by
  have : NeZero (M + 1) := ⟨Nat.succ_ne_zero M⟩
  have hψ0 : ψ ≠ 0 := by rintro rfl; simp at hψ
  obtain ⟨p₀⟩ := (inferInstance : Nonempty (CPN (M + 1)))
  rw [fsMeasure_unique p₀ μ hμ, freeMoment_eq_ratioN, ← ratioN_momentMap_mk ψ hψ0 hψ,
    fsMeasure_preimage_apexCell p₀ ψ hψ0 hψ, EuclideanSpace.inner_single_left, map_one,
    one_mul]
end BornVolume
