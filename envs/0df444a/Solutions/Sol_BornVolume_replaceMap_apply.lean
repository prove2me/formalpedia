-- Prove2me | solution 1 for BornVolume.replaceMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:29.82541+00:00
-- url     : https://prove2.me/submissions/561e723a-8261-40aa-b3c8-174739dfb589

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_VertexReplacement
public import Definitions.Def_BornVolumeLean_Volume_CellMeasurePos

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution {N : ℕ} (b : Fin N → ℝ) (i : Fin N) (t : Fin N → ℝ) (k : Fin N) :
    (replaceMap b i) t k = b k * t i + (if k = i then 0 else t k) := by
  classical
  rw [replaceMap, Matrix.toLin'_apply]
  show (∑ j, ((1 : Matrix (Fin N) (Fin N) ℝ).updateCol i b) k j * t j) = _
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), Matrix.updateCol_apply, if_pos rfl]
  congr 1
  rw [Finset.sum_congr rfl (fun j hj => by
    rw [Matrix.updateCol_apply, if_neg (Finset.ne_of_mem_erase hj), Matrix.one_apply, ite_mul,
      one_mul, zero_mul]),
    Finset.sum_ite_eq (Finset.univ.erase i) k t]
  by_cases hk : k = i <;> simp [Finset.mem_erase, hk]
end BornVolume
