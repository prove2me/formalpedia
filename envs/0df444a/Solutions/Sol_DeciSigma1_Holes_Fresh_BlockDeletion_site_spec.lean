-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.site_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:48:49.150289+00:00
-- url     : https://prove2.me/submissions/ae4c5aaf-3eb9-4f9f-9e14-dc6099b1e483

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_one_le_minDepth
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_maxDepth_lt_endDepth
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_depthCut_through
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_through_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_lt_of_lt
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_spec


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) (hth : m.edge.TraversedBy o) :
    o.2.1 < depthCut W t o m.maxDepth ∧ depthCut W t o m.maxDepth < depthCut W t o m.minDepth ∧
      depthCut W t o m.minDepth < o.2.2 ∧ o.2.2 ≤ (W o.1).length ∧
      depthCut W t o m.maxDepth + m.deletionLength = depthCut W t o m.minDepth ∧
      depthCut W t o m.maxDepth ∈ anchors W t o.1 ∧ depthCut W t o m.minDepth ∈
          anchors W t o.1 := by
  have hbn := (m.edge.through_iff.mp hth).1
  have hjn : m.maxDepth < lowerBlockCount W t o := lt_of_lt_of_le m.maxDepth_lt_endDepth hbn
  have hin : m.minDepth < lowerBlockCount W t o := by have := m.minDepth_lt_maxDepth; omega
  obtain ⟨hall, -⟩ := depthCut_spec ho
  obtain ⟨hjA, hjs, -, -⟩ := hall m.maxDepth hjn
  obtain ⟨hiA, -, -, -⟩ := hall m.minDepth hin
  have hji := depthCut_lt_of_lt ho m.minDepth_lt_maxDepth hjn.le
  have hie : depthCut W t o m.minDepth < o.2.2 :=
    depthCut_lt_of_lt ho (show 0 < m.minDepth from m.one_le_minDepth) hin.le
  have hj' := m.edge.depthCut_through ho hth m.maxDepth_lt_endDepth.le
  have hi' := m.edge.depthCut_through ho hth (d := m.minDepth)
    (by have := m.minDepth_lt_maxDepth; have := m.maxDepth_lt_endDepth; omega)
  have hE := (upperOcc_spec ho).2.1
  refine ⟨hjs, hji, hie, hE, ?_, hjA, hiA⟩
  unfold deletionLength
  omega
end DeciSigma1.Holes.Fresh.BlockDeletion
