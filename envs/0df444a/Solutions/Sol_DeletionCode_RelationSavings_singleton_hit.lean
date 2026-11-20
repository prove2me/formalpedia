-- Prove2me | solution 1 for DeletionCode.RelationSavings.singleton_hit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:27:51.522529+00:00
-- url     : https://prove2.me/submissions/2ddd1447-68be-4cca-aed1-9fa24a56c08b

import Definitions.Def_DeletionCode_CatalogueFamily
import Definitions.Def_DeletionCode_ComponentFibers
import Definitions.Def_DeletionCode_RelationSupport
import Definitions.Def_DeletionCode_SupportInclusion
import Definitions.Def_DeletionCode_RelationSavings
import Theorems.Thm_DeletionCode_RelationSavings_singleton_coordinate
import Theorems.Thm_DeletionCode_RelationSupport_isolated_coordinate_nonzero


set_option autoImplicit true
open DeletionCode DeletionCode.RelationSavings
open HeaderRecovery SignedSupport RuleReconstruction RuleSetGraph SupportComponents
open SignedRuleCount ConnectedBlocks CatalogueFamily ComponentFibers SupportInclusion
open scoped BigOperators
variable {t k R : ℕ} {G : Fin R → Gram (windowLength k) → ℤ}
namespace DeletionCode.RelationSavings
theorem _root_.solution (P : PresentedFamily t k R G)
    (w : Gram (windowLength k) → ℤ) (a : Fin R → ℚ)
    (hrel : RelationSupport.Relation G w a) (ha : ∀ r, a r ≠ 0)
    (C : RuleSetComponents (Finset.univ.image G))
    (hC : SingletonFiber P.bubbleComponent C) :
    ∃ v : RuleSetVertex {w},
      supportComponentMap (relation_support_included w a hrel)
        (Quotient.mk (ruleSetSetoid {w}) v) = C := by
  classical
  obtain ⟨r, g, hrg, hother, hv, hcomp⟩ := singleton_coordinate P C hC
  have hwg := RelationSupport.isolated_coordinate_nonzero G w a hrel r g (ha r) hrg hother
  have hwv : Incident {w} (gramPrefix g) :=
    ⟨gramSuffix g, Or.inl ⟨w, Finset.mem_singleton_self w, g, hwg, rfl, rfl⟩⟩
  exact ⟨⟨gramPrefix g, hwv⟩, hcomp⟩
end DeletionCode.RelationSavings
