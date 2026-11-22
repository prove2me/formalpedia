-- Prove2me | solution 1 for BornVolume.fsMeasure_preimage_apexCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:42.139229+00:00
-- url     : https://prove2.me/submissions/605f76ee-9752-4ad3-9a13-2f0b2d6cc0b2

module
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Theorems.Thm_BornVolume_apexMap_image_measurableSet
public import Theorems.Thm_BornVolume_fs_volume_eq_dirichlet_inter
public import Theorems.Thm_BornVolume_apexMap_image_subset_of_closedSimplex
public import Theorems.Thm_BornVolume_apexMap_image_volume
public import Theorems.Thm_BornVolume_apexLin_det
public import Theorems.Thm_BornVolume_apexLin_image_isOpen
public import Theorems.Thm_BornVolume_fs_volume_eq_dirichlet
public import Theorems.Thm_BornVolume_one_sub_sum_ratioN_momentMap
public import Theorems.Thm_BornVolume_ratioN_momentMap_castSucc
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
    (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) :
    fsMeasure p₀
        ((fun p => ratioN (fun j => momentMap p j))
          ⁻¹' ((fun x => apexLin (ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)) x
              + ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)) '' openSimplexFree))
      = ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single (Fin.last M) (1 : ℂ)) ψ‖ ^ 2) := by
  set b : Fin M → ℝ := ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) with hb
  have hlast : (1 : ℝ) - ∑ k, b k
      = ‖inner ℂ (EuclideanSpace.single (Fin.last M) (1 : ℂ)) ψ‖ ^ 2 := by
    have h := one_sub_sum_ratioN_momentMap ψ hψ0 hψ
    rw [← hb] at h
    exact h
  have hb0 : ∀ k, 0 ≤ b k := fun k => by
    rw [hb, ratioN_momentMap_castSucc ψ hψ0 hψ k]; positivity
  have hb_nonneg : 0 ≤ 1 - ∑ k, b k := by rw [hlast]; positivity
  rcases hb_nonneg.lt_or_eq with hpos | hzero
  · -- positive branch: apex weight 1 − ∑b > 0 (= the subset lemma's hypothesis).
    have hbsum : ∑ k, b k < 1 := by linarith
    have hdet : LinearMap.det (apexLin b) ≠ 0 := by
      rw [apexLin_det]; exact ne_of_gt hpos
    rw [fs_volume_eq_dirichlet p₀ (apexLin_image_isOpen b hdet).measurableSet
        (apexMap_image_subset_of_closedSimplex b hb0 hbsum),
      apexMap_image_volume b hb_nonneg, volume_openSimplexFree, hlast]
    have hfac : (Nat.factorial M : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero M
    have hfac_top : (Nat.factorial M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [← mul_assoc, mul_comm (Nat.factorial M : ℝ≥0∞)
        (ENNReal.ofReal (‖inner ℂ (EuclideanSpace.single (Fin.last M) (1 : ℂ)) ψ‖ ^ 2)),
      mul_assoc, ENNReal.mul_inv_cancel hfac hfac_top, mul_one]
  · -- zero branch: ∑b = 1 ⟹ det (apexLin b) = 0 ⟹ null cell = Born weight 0.
    have hvol : volume ((fun x => apexLin b x + b) '' openSimplexFree) = 0 := by
      rw [apexMap_image_volume b hb_nonneg, ← hzero, ENNReal.ofReal_zero, zero_mul]
    have hinter :
        volume (((fun x => apexLin b x + b) '' openSimplexFree) ∩ openSimplexFree) = 0 :=
      measure_mono_null Set.inter_subset_left hvol
    rw [fs_volume_eq_dirichlet_inter p₀ (apexMap_image_measurableSet b), hinter,
      mul_zero, ← hlast, ← hzero, ENNReal.ofReal_zero]
end BornVolume
