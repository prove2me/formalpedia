-- Prove2me | solution 1 for DeletionCode.GeneratingEnumeration.CataloguePresentation.signedGenerating
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:25:37.937725+00:00
-- url     : https://prove2.me/submissions/e3d76d17-220e-4645-a493-51b3e66e3b6b

import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_ManuscriptCounting
import Definitions.Def_DeletionCode_CatalogueFamily
import Mathlib.Data.Finset.Sort
import Definitions.Def_DeletionCode_GeneratingEnumeration
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_geometry
import Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_rank_disjoint
import Theorems.Thm_DeletionCode_SignedSupport_rule_support_iff


set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingEnumeration
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph SupportComponents
open CanonicalIndex ConnectedBlocks FiniteGenerating
open scoped BigOperators
namespace DeletionCode.GeneratingEnumeration
namespace CataloguePresentation
theorem _root_.solution {t k R : ℕ}
    {rules : Fin R → Gram (windowLength k) → ℤ} (P : CataloguePresentation t k R rules)
    (x : Letters) (n : ℕ)
    (hgen : ∀ i g, rules i g = -1 → wordSpectrum x n (windowLength k) g ≠ 0 ∨
      ∃ j : Fin R, j < i ∧ rules j g ≠ 0) :
    SignedGenerating (flatFamily t R P.words).family x n (windowLength k) := by
  let E := flatFamily t R P.words
  have hrank : ∀ b, E.rank b = (group t R b).val := fun _ => rfl
  have heq (r : Fin R) :
      ruleSpectrum E.family (windowLength k) (ruleBubbles E.family r.val) = rules r := by
    rw [rank_bubbles_eq_group E (group t R) hrank r]
    exact P.rule_eq r
  intro i g hneg
  have hnonzero : ruleSpectrum E.family (windowLength k) (ruleBubbles E.family i) g ≠ 0 := by
    change ruleSpectrum E.family (windowLength k) (ruleBubbles E.family i) g = -1 at hneg
    omega
  obtain ⟨b, hb, _⟩ := (rule_support_iff E.family (windowLength k) P.valid.geometry
    (ruleBubbles E.family i) (P.valid.rank_disjoint i) g).mp hnonzero
  have hbi : E.rank b = i := (Finset.mem_filter.mp hb).2
  have hi : i < R := by
    rw [hrank b] at hbi
    exact hbi ▸ (group t R b).isLt
  let r : Fin R := ⟨i, hi⟩
  have hrneg : rules r g = -1 := by
    rw [← heq r]
    exact hneg
  rcases hgen r g hrneg with hv | ⟨j, hj, hjg⟩
  · exact Or.inl hv
  · refine Or.inr ⟨j.val, hj, ?_⟩
    rw [heq j]
    exact hjg
end CataloguePresentation
end DeletionCode.GeneratingEnumeration
