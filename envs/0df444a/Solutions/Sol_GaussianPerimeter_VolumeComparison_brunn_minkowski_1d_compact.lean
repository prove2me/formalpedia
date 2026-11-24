-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.brunn_minkowski_1d_compact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:20:06.122855+00:00
-- url     : https://prove2.me/submissions/4936c5ff-67b2-45e9-b29c-dc7610bb7d64

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution
    {A B C : Set ℝ}
    (h : A + B ⊆ C)
    (hA_nonempty : A.Nonempty) (hA_compact : IsCompact A)
    (hB_nonempty : B.Nonempty) (hB_compact : IsCompact B)
    : volume A + volume B ≤ volume C := by
  -- Translate A, B to A', B' so that their intersection is {0}
  let A' := A + {-sSup A}
  let B' := B + {-sInf B}
  have h_inter_zero : A' ∩ B' = {0} := by
    ext x
    simp only [add_singleton, image_add_right, neg_neg, mem_inter_iff, mem_preimage,
      mem_singleton_iff, A', B']
    constructor
    · intro ⟨ha, hb⟩
      exact le_antisymm
        (nonpos_of_add_le_left (le_csSup hA_compact.bddAbove ha))
        (nonneg_of_le_add_left (csInf_le hB_compact.bddBelow hb))
    · intro hx
      simp only [hx, zero_add]
      exact ⟨hA_compact.sSup_mem hA_nonempty, hB_compact.sInf_mem hB_nonempty⟩
  calc
    volume C ≥ volume (A + B) := measure_mono h
    -- Replacing A+B with A'+B' preserves volume
    _ = volume (A + B + {-sSup A} + {-sInf B}) := by simp
    _ = volume (A' + B') := by
      congr 1; nth_rw 2 [add_assoc]; nth_rw 3 [add_comm]; rw [← add_assoc]; rw [add_assoc]
    -- The volume of A'+B' is at least that of A'∪B', since both A' and B' contain 0.
    _ ≥ volume (A' ∪ B') := by
      apply measure_mono
      rw [union_subset_iff]
      have h_zero_in_inter : 0 ∈ A' ∩ B' := by simp [h_inter_zero]
      exact ⟨subset_add_left A' h_zero_in_inter.2, subset_add_right B' h_zero_in_inter.1⟩
    -- Finish the proof using the fact that A' and B' have intersection {0}
    -- and using translation invariance of volume.
    _ = volume (A' ∪ B') + volume (A' ∩ B') := by simp [h_inter_zero]
    _ = volume A' + volume B' := by
      rw [measure_union_add_inter]
      exact (hB_compact.add isCompact_singleton).measurableSet
    _ = volume A + volume B := by simp [A', B']
end GaussianPerimeter.VolumeComparison
