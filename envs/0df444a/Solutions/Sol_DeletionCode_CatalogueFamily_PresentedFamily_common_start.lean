-- Prove2me | solution 1 for DeletionCode.CatalogueFamily.PresentedFamily.common_start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:22:28.123183+00:00
-- url     : https://prove2.me/submissions/805d3699-7b24-4251-9a82-981d1db617f4

import Definitions.Def_DeletionCode_ConnectedBlocks
import Definitions.Def_DeletionCode_CanonicalIndex
import Definitions.Def_DeletionCode_CatalogueFamily
import Theorems.Thm_DeletionCode_PathMemory_pathInitialAgreement


set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueFamily
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph SupportComponents
open CanonicalIndex ConnectedBlocks
open scoped BigOperators
open DeletionCode.CatalogueFamily.PresentedFamily
variable {t k R : ℕ} {G : Fin R → Gram (windowLength k) → ℤ}
namespace DeletionCode.CatalogueFamily.PresentedFamily
theorem _root_.solution (P : PresentedFamily t k R G) (b : Fin (2 * t * R)) :
    vertex P.E.family (windowLength k) b false 0 =
      vertex P.E.family (windowLength k) b true 0 := by
  apply (vertex_eq_iff_agree P.E.family (windowLength k) b b false true 0 0).mpr
  exact PathMemory.pathInitialAgreement k (P.E.header b) (P.E.long b)
end DeletionCode.CatalogueFamily.PresentedFamily
