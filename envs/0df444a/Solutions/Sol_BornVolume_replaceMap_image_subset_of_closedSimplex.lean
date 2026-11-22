-- Prove2me | solution 1 for BornVolume.replaceMap_image_subset_of_closedSimplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:04.280827+00:00
-- url     : https://prove2.me/submissions/d70c78c9-98c1-49af-b638-6f3086a16868

module
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Theorems.Thm_BornVolume_replaceMap_apply


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (b : Fin M → ℝ) (i : Fin M)
    (hb0 : ∀ k, 0 ≤ b k) (hbsum : ∑ k, b k ≤ 1) (hbi : 0 < b i) :
    (replaceMap b i) '' openSimplexFree ⊆ openSimplexFree := by
  rintro _ ⟨t, ⟨htpos, htsum⟩, rfl⟩
  have hcompl : ∑ k, (if k = i then (0 : ℝ) else t k) = (∑ k, t k) - t i := by
    have h1 : ∑ k, ((if k = i then (0 : ℝ) else t k) + (if i = k then t k else 0)) = ∑ k, t k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases hk : k = i
      · subst hk; simp
      · rw [if_neg hk, if_neg (Ne.symm hk), add_zero]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ i t,
      if_pos (Finset.mem_univ i)] at h1
    linarith
  refine ⟨fun k => ?_, ?_⟩
  · rw [replaceMap_apply]
    by_cases hk : k = i
    · rw [if_pos hk, add_zero, hk]
      exact mul_pos hbi (htpos i)
    · rw [if_neg hk]
      have hbk := mul_nonneg (hb0 k) (le_of_lt (htpos i))
      linarith [htpos k]
  · rw [Finset.sum_congr rfl (fun k _ => replaceMap_apply b i t k), Finset.sum_add_distrib,
      ← Finset.sum_mul, hcompl]
    nlinarith [htsum, mul_nonneg (sub_nonneg.mpr hbsum) (le_of_lt (htpos i))]
end BornVolume
