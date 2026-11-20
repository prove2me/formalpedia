-- Prove2me | solution 1 for DeletionCode.CatalogueVertexBound.bubble_vertex_names_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:38.342427+00:00
-- url     : https://prove2.me/submissions/84535e36-e577-4be1-8a8e-d2d1abb6eefa

import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_DeletionCode_CatalogueVertexBound

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueVertexBound
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport RuleReconstruction RuleSetGraph SupportComponents ConnectedBlocks
open scoped BigOperators
namespace DeletionCode.CatalogueVertexBound
theorem _root_.solution {t k : ℕ} (E : EditedFamily (Fin (2 * t)) k)
    (b : Fin (2 * t)) :
    E.family.extra b false + 2 + (E.family.extra b true + 1) ≤ 2 * windowLength k := by
  have hlo := E.rho_lower b
  have hhi := E.rho_upper b
  cases ho : (E.header b).orientation <;>
    simp only [EditedFamily.family, PathMemory.pathLength, Bool.false_eq_true,
      ite_false, ite_true, negativeLength, positiveLength, shortLength, longLength,
      windowLength, ho] <;> omega
end DeletionCode.CatalogueVertexBound
