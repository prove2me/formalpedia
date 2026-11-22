-- Prove2me | solution 1 for BornVolume.fs_volume_eq_dirichlet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:34.461867+00:00
-- url     : https://prove2.me/submissions/5856b323-b45b-4f2a-b5da-ce81d4154104

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
theorem _root_.solution (p₀ : CPN (M + 1)) {R : Set (Fin M → ℝ)}
    (hR : MeasurableSet R) (hRsub : R ⊆ openSimplexFree) :
    fsMeasure p₀ ((fun p => ratioN (fun i => momentMap p i)) ⁻¹' R)
      = (Nat.factorial M : ℝ≥0∞) * volume R := by
  rw [← Measure.map_apply measurable_ratio_momentMap hR, map_ratioN_momentMap_fsMeasure,
    Measure.smul_apply, Measure.restrict_apply hR, smul_eq_mul,
    Set.inter_eq_left.mpr hRsub]
end BornVolume
