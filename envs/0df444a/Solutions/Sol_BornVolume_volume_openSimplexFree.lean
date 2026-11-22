-- Prove2me | solution 1 for BornVolume.volume_openSimplexFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:34.889486+00:00
-- url     : https://prove2.me/submissions/fdfcbcc3-0519-4408-b7ac-2acceca0ea52

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_VertexReplacement
public import Definitions.Def_BornVolumeLean_Volume_CellMeasurePos
public import Theorems.Thm_BornVolume_measurable_ratio_momentMap
public import Theorems.Thm_BornVolume_map_ratioN_momentMap_fsMeasure


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution :
    volume (openSimplexFree (M := M)) = (Nat.factorial M : ℝ≥0∞)⁻¹ := by
  set p₀ : CPN (M + 1) :=
    Projectivization.mk ℂ (EuclideanSpace.single (0 : Fin (M + 1)) (1 : ℂ))
      (by simp [EuclideanSpace.single]) with hp₀
  have hkey : (Nat.factorial M : ℝ≥0∞) * volume (openSimplexFree (M := M)) = 1 := by
    have h := congrArg (fun μ : Measure (Fin M → ℝ) => μ Set.univ)
      (map_ratioN_momentMap_fsMeasure p₀)
    simp only [Measure.map_apply measurable_ratio_momentMap MeasurableSet.univ,
      Set.preimage_univ, measure_univ, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, smul_eq_mul] at h
    exact h.symm
  have hfac : (Nat.factorial M : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero M
  have hfac_top : (Nat.factorial M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc volume (openSimplexFree (M := M))
      = ((Nat.factorial M : ℝ≥0∞)⁻¹ * (Nat.factorial M : ℝ≥0∞)) * volume (openSimplexFree (M := M)) := by
        rw [ENNReal.inv_mul_cancel hfac hfac_top, one_mul]
    _ = (Nat.factorial M : ℝ≥0∞)⁻¹ * ((Nat.factorial M : ℝ≥0∞) * volume (openSimplexFree (M := M))) := by
        rw [mul_assoc]
    _ = (Nat.factorial M : ℝ≥0∞)⁻¹ := by rw [hkey, mul_one]
end BornVolume
