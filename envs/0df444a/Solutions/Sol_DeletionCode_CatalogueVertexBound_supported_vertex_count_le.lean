-- Prove2me | solution 1 for DeletionCode.CatalogueVertexBound.supported_vertex_count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:40.483291+00:00
-- url     : https://prove2.me/submissions/a89d864d-cfcc-4cf2-bf1c-e9b4053594f1

import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_DeletionCode_CatalogueVertexBound
import Theorems.Thm_DeletionCode_CatalogueVertexBound_namedVertex_surjective
import Theorems.Thm_DeletionCode_CatalogueVertexBound_bubble_vertex_names_le

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueVertexBound
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport RuleReconstruction RuleSetGraph SupportComponents ConnectedBlocks
open scoped BigOperators
namespace DeletionCode.CatalogueVertexBound
theorem _root_.solution {t k : ℕ} (E : EditedFamily (Fin (2 * t)) k) :
    Nat.card (SupportedVertex E.family (windowLength k)) ≤ 4 * t * windowLength k := by
  classical
  letI : Fintype (SupportedVertex E.family (windowLength k)) := by
    unfold SupportedVertex
    infer_instance
  have hnames : Fintype.card (VertexNames E) ≤ (2 * t) * (2 * windowLength k) := by
    rw [Fintype.card_sigma]
    calc
      (∑ b : Fin (2 * t),
          Fintype.card (Fin (E.family.extra b false + 2) ⊕
            Fin (E.family.extra b true + 1))) ≤
          ∑ _b : Fin (2 * t), 2 * windowLength k := by
        apply Finset.sum_le_sum
        intro b hb
        simpa only [Fintype.card_sum, Fintype.card_fin] using bubble_vertex_names_le E b
      _ = (2 * t) * (2 * windowLength k) := by simp
  have hcard := Fintype.card_le_of_surjective (namedVertex E) (namedVertex_surjective E)
  calc
    Nat.card (SupportedVertex E.family (windowLength k)) =
        Fintype.card (SupportedVertex E.family (windowLength k)) := Nat.card_eq_fintype_card
    _ ≤ (2 * t) * (2 * windowLength k) := hcard.trans hnames
    _ = 4 * t * windowLength k := by ring
end DeletionCode.CatalogueVertexBound
