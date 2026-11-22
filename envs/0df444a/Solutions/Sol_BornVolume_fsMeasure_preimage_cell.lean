-- Prove2me | solution 1 for BornVolume.fsMeasure_preimage_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:41.691337+00:00
-- url     : https://prove2.me/submissions/d86f7c3d-b4d2-4012-b7c8-47bad1011078

module
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Theorems.Thm_BornVolume_replaceMap_image_measurableSet
public import Theorems.Thm_BornVolume_fs_volume_eq_dirichlet_inter
public import Theorems.Thm_BornVolume_replaceMap_image_subset_of_closedSimplex
public import Theorems.Thm_BornVolume_fs_volume_eq_dirichlet
public import Theorems.Thm_BornVolume_one_sub_sum_ratioN_momentMap
public import Theorems.Thm_BornVolume_ratioN_momentMap_castSucc
public import Theorems.Thm_BornVolume_replaceMap_det
public import Theorems.Thm_BornVolume_replaceMap_image_isOpen
public import Theorems.Thm_BornVolume_replaceMap_image_volume
public import Theorems.Thm_BornVolume_volume_openSimplexFree


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (p₀ : CPN (M + 1))
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) (i : Fin M) :
    fsMeasure p₀
        ((fun p => ratioN (fun j => momentMap p j))
          ⁻¹' (replaceMap (ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)) i
            '' openSimplexFree))
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ)) ψ‖ ^ 2) := by
  set b : Fin M → ℝ := ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) with hb
  have hbi : b i = ‖inner ℂ (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ)) ψ‖ ^ 2 := by
    rw [hb]; exact ratioN_momentMap_castSucc ψ hψ0 hψ i
  have hb0 : ∀ k, 0 ≤ b k := fun k => by
    rw [hb, ratioN_momentMap_castSucc ψ hψ0 hψ k]; positivity
  have hbsum : ∑ k, b k ≤ 1 := by
    have h := one_sub_sum_ratioN_momentMap ψ hψ0 hψ
    rw [← hb] at h
    linarith [sq_nonneg ‖inner ℂ (EuclideanSpace.single (Fin.last M) (1 : ℂ)) ψ‖]
  rcases (hb0 i).lt_or_eq with hbi_pos | hbi_zero
  · -- positive branch: det = b i ≠ 0, so the image is open and lies in the simplex.
    have hdet : LinearMap.det (replaceMap b i) ≠ 0 := by
      rw [replaceMap_det]; exact ne_of_gt hbi_pos
    rw [fs_volume_eq_dirichlet p₀ (replaceMap_image_isOpen b i hdet).measurableSet
        (replaceMap_image_subset_of_closedSimplex b i hb0 hbsum hbi_pos),
      replaceMap_image_volume b i (hb0 i), volume_openSimplexFree, hbi]
    have hfac : (Nat.factorial M : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero M
    have hfac_top : (Nat.factorial M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [← mul_assoc, mul_comm (Nat.factorial M : ℝ≥0∞)
        (ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single (Fin.castSucc i) (1 : ℂ)) ψ‖ ^ 2)),
      mul_assoc, ENNReal.mul_inv_cancel hfac hfac_top, mul_one]
  · -- zero branch: det = 0 ⟹ the cell is Lebesgue-null ⟹ FS-null = Born weight.
    have hvol : volume ((replaceMap b i) '' openSimplexFree) = 0 := by
      rw [replaceMap_image_volume b i (hb0 i), ← hbi_zero, ENNReal.ofReal_zero, zero_mul]
    have hinter : volume ((replaceMap b i '' openSimplexFree) ∩ openSimplexFree) = 0 :=
      measure_mono_null Set.inter_subset_left hvol
    rw [fs_volume_eq_dirichlet_inter p₀ (replaceMap_image_measurableSet b i), hinter,
      mul_zero, ← hbi, ← hbi_zero, ENNReal.ofReal_zero]
end BornVolume
