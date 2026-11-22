-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.active_of_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:46:56.140661+00:00
-- url     : https://prove2.me/submissions/3089cef6-d498-4494-b006-4795983af0e5

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_maxDepth_lt_endDepth
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_one_le_minDepth
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_through_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_eq_singleton
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchors_succ_subset
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_lt
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_succ_succ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_ne_nil_of_mem_upperOccurrences
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_spec
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : m.edge.TraversedBy o) : o.1 ∈ active W (t + 1) := by
  have hbn := (m.edge.through_iff.mp hth).1
  have h2 : 1 <
      lowerBlockCount W t o := by have := m.maxDepth_lt_endDepth; have := m.one_le_minDepth;
                                  have := m.minDepth_lt_maxDepth; omega
  obtain ⟨hall, -⟩ := depthCut_spec ho
  obtain ⟨hA, -, -, -⟩ := hall 1 h2
  have hlt : depthCut W t o 1 < depthCut W t o 0 := depthCut_lt ho (d := 0) (by omega)
  have hE := (upperOcc_spec ho).2.1
  have hd0 : depthCut W t o 0 = o.2.2 := rfl
  rcases t with _ | t
  · exact (mem_active_one W).mpr (ne_nil_of_mem_upperOccurrences ho)
  · by_cases hact : o.1 ∈ active W (t + 1)
    · exact (mem_active_succ_succ W).mpr ⟨hact, _, hA, by omega⟩
    · exfalso
      rcases t with _ | t
      · exact hact ((mem_active_one W).mpr (ne_nil_of_mem_upperOccurrences ho))
      · have hsing := anchors_eq_singleton (t := t + 1) (by omega) hact
        have := anchors_succ_subset (t + 1) o.1 hA
        rw [hsing, mem_singleton] at this
        omega
end DeciSigma1.Holes.Fresh.BlockDeletion
