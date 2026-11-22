-- Prove2me | solution 1 for BornVolume.born_vector_uniform_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:42.548463+00:00
-- url     : https://prove2.me/submissions/09bdc45d-242a-492f-b645-78b0cc1beaae

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Theorems.Thm_BornVolume_map_momentMap_fsMeasure
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
    (hμ : ∀ U : Matrix.unitaryGroup (Fin (M + 1)) ℂ, Measure.map (fun p => U • p) μ = μ) :
    Measure.map (fun (p : CPN (M + 1)) (k : Fin M) => momentMap p (Fin.castSucc k)) μ
      = (Nat.factorial M : ℝ≥0∞) • volume.restrict openSimplexFree := by
  have : NeZero (M + 1) := ⟨Nat.succ_ne_zero M⟩
  obtain ⟨p₀⟩ := (inferInstance : Nonempty (CPN (M + 1)))
  rw [fsMeasure_unique p₀ μ hμ]
  exact map_momentMap_fsMeasure p₀
end BornVolume
