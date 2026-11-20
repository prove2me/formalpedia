-- Prove2me | solution 1 for DeletionCode.CatalogueBridge.differentLengths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:22.130453+00:00
-- url     : https://prove2.me/submissions/ea4102a0-434b-4b93-a9b3-4d608b0bebef

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_CatalogueBridge

set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueBridge
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport
open RuleReconstruction SignedRuleCount DescriptionCount
namespace DeletionCode.CatalogueBridge
theorem _root_.solution {B : Type*} {k : ℕ} (E : EditedFamily B k) (b : B) :
    E.family.extra b false ≠ E.family.extra b true := by
  have hlo := E.rho_lower b
  have hhi := E.rho_upper b
  cases ho : (E.header b).orientation <;>
    simp only [EditedFamily.family, PathMemory.pathLength, Bool.false_eq_true,
      ite_false, ite_true, negativeLength, positiveLength, shortLength, longLength,
      windowLength, ho] <;> omega
end DeletionCode.CatalogueBridge
