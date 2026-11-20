-- Prove2me | solution 1 for DeletionCode.CatalogueVertexBound.namedVertex_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:10.912665+00:00
-- url     : https://prove2.me/submissions/06af110a-48f5-44af-b74d-084082287788

import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_DeletionCode_CatalogueVertexBound
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm


set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueVertexBound
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport RuleReconstruction RuleSetGraph SupportComponents ConnectedBlocks
open scoped BigOperators
namespace DeletionCode.CatalogueVertexBound
theorem _root_.solution {t k : ℕ} (E : EditedFamily (Fin (2 * t)) k) :
    Function.Surjective (namedVertex E) := by
  intro v
  obtain ⟨b, side, i, hi, hv⟩ := v.property
  cases side with
  | false =>
    refine ⟨⟨b, Sum.inl ⟨i, by omega⟩⟩, ?_⟩
    apply Subtype.ext
    exact hv.symm
  | true =>
    by_cases hzero : i = 0
    · subst i
      refine ⟨⟨b, Sum.inl ⟨0, by omega⟩⟩, ?_⟩
      apply Subtype.ext
      change vertex E.family (windowLength k) b false 0 = v.val
      rw [GeneratingRecovery.initial_vertices_agree E b]
      exact hv.symm
    · refine ⟨⟨b, Sum.inr ⟨i - 1, by omega⟩⟩, ?_⟩
      apply Subtype.ext
      change vertex E.family (windowLength k) b true (i - 1 + 1) = v.val
      have hindex : i - 1 + 1 = i := by omega
      rw [hindex]
      exact hv.symm
end DeletionCode.CatalogueVertexBound
