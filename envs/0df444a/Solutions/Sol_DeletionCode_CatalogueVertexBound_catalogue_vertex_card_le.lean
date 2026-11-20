-- Prove2me | solution 1 for DeletionCode.CatalogueVertexBound.catalogue_vertex_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:23:47.374389+00:00
-- url     : https://prove2.me/submissions/cf9e368d-41c7-49d5-9971-5e36d32c287f

import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_DeletionCode_CatalogueVertexBound
import Theorems.Thm_DeletionCode_CatalogueVertexBound_supported_vertex_count_le
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_rank_disjoint
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm

section
namespace DeletionCode.CatalogueVertexBound
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport RuleReconstruction RuleSetGraph SupportComponents ConnectedBlocks
open scoped BigOperators
private theorem singleton_rules {t k : ℕ} (words : Fin (2 * t) → BubbleWord k)
    (w : Gram (windowLength k) → ℤ)
    (hvalue : ruleSpectrum (indexedFamily words (fun _ => (0 : Fin 1))).family
      (windowLength k) Finset.univ = w) :
    rulesOfFamily (indexedFamily words (fun _ => (0 : Fin 1)))
      (fun _ => (0 : Fin 1)) = {w} := by
  classical
  have hgroup (r : Fin 1) :
      groupBubbles (fun _ : Fin (2 * t) => (0 : Fin 1)) r = Finset.univ := by
    have hr : r = 0 := Subsingleton.elim _ _
    subst r
    simp [groupBubbles]
  ext f
  simp only [rulesOfFamily, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨r, hf⟩
    rw [hgroup r, hvalue] at hf
    exact hf.symm
  · intro hf
    refine ⟨0, ?_⟩
    rw [hgroup 0, hvalue, hf]
end DeletionCode.CatalogueVertexBound
end

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueVertexBound
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport RuleReconstruction RuleSetGraph SupportComponents ConnectedBlocks
open scoped BigOperators
namespace DeletionCode.CatalogueVertexBound
theorem _root_.solution {t k : ℕ}
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w) :
    Fintype.card (RuleSetVertex {w}) ≤ 4 * t * windowLength k := by
  obtain ⟨words, hvalid, _, hvalue⟩ := hw
  let E := indexedFamily words (fun _ => (0 : Fin 1))
  have hQ : rulesOfFamily E (fun _ => (0 : Fin 1)) = {w} :=
    singleton_rules words w hvalue
  let e : RuleSetVertex {w} ≃ SupportedVertex E.family (windowLength k) := by
    rw [← hQ]
    exact incidentVertexEquiv E (fun _ => (0 : Fin 1)) (fun _ => rfl)
      hvalid.geometry hvalid.rank_disjoint
  calc
    Fintype.card (RuleSetVertex {w}) = Nat.card (RuleSetVertex {w}) :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card (SupportedVertex E.family (windowLength k)) := Nat.card_congr e
    _ ≤ 4 * t * windowLength k := supported_vertex_count_le E
end DeletionCode.CatalogueVertexBound
