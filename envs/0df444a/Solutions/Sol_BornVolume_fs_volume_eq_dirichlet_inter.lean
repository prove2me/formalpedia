-- Prove2me | solution 1 for BornVolume.fs_volume_eq_dirichlet_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:35.299592+00:00
-- url     : https://prove2.me/submissions/2a74e9d3-8b61-46ea-bf8b-3d98dc4be279

module
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Theorems.Thm_BornVolume_map_ratioN_momentMap_fsMeasure
public import Theorems.Thm_BornVolume_measurable_ratio_momentMap


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (p₀ : CPN (M + 1)) {R : Set (Fin M → ℝ)}
    (hR : MeasurableSet R) :
    fsMeasure p₀ ((fun p => ratioN (fun i => momentMap p i)) ⁻¹' R)
      = (Nat.factorial M : ℝ≥0∞) * volume (R ∩ openSimplexFree) := by
  rw [← Measure.map_apply measurable_ratio_momentMap hR, map_ratioN_momentMap_fsMeasure,
    Measure.smul_apply, Measure.restrict_apply hR, smul_eq_mul]
end BornVolume
