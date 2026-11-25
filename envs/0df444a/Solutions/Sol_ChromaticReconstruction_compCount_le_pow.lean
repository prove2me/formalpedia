-- Prove2me | solution 1 for ChromaticReconstruction.compCount_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:49:04.060953+00:00
-- url     : https://prove2.me/submissions/ae1aa648-ccf4-445b-bfd7-d7ebd728a6fd

import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_CountingUpper
import Theorems.Thm_ChromaticReconstruction_card_compSets_add_card_of_isTree
import Theorems.Thm_ChromaticReconstruction_card_compType


set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {k t : ℕ} {S : SimpleGraph (Fin k)} (hS : S.IsTree)
    {μ : Nat.Partition k} (hμ : k - t ≤ Multiset.card μ.parts) :
    compCount S μ.parts ≤ k ^ t := by
  unfold compCount
  have hsub : S.edgeFinset.powerset.filter
      (fun F : Finset (Sym2 (Fin k)) => compType (↑F : Set (Sym2 (Fin k))) = μ.parts) ⊆
      S.edgeFinset.powersetCard (k - Multiset.card μ.parts) := by
    intro F hF
    rw [mem_filter, mem_powerset] at hF
    rw [mem_powersetCard]
    refine ⟨hF.1, ?_⟩
    have h1 := card_compSets_add_card_of_isTree hS hF.1
    have h2 := card_compType (F : Set (Sym2 (Fin k)))
    rw [hF.2] at h2
    rw [Fintype.card_fin] at h1
    omega
  refine (card_le_card hsub).trans ?_
  rw [card_powersetCard]
  have hE := hS.card_edgeFinset
  rw [Fintype.card_fin] at hE
  refine (Nat.choose_le_pow _ _).trans ?_
  have hk : 1 ≤ k := by omega
  calc S.edgeFinset.card ^ (k - Multiset.card μ.parts)
      ≤ k ^ (k - Multiset.card μ.parts) := Nat.pow_le_pow_left (by omega) _
    _ ≤ k ^ t := Nat.pow_le_pow_right hk (by omega)
end ChromaticReconstruction
