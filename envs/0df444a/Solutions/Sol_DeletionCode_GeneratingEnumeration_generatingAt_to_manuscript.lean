-- Prove2me | solution 1 for DeletionCode.GeneratingEnumeration.generatingAt_to_manuscript
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:32:49.407009+00:00
-- url     : https://prove2.me/submissions/03120ccd-3df3-4dca-a7ed-fe3c7ebfaa0b

import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_ManuscriptCounting
import Definitions.Def_DeletionCode_CatalogueFamily
import Mathlib.Data.Finset.Sort
import Definitions.Def_DeletionCode_GeneratingEnumeration
import Theorems.Thm_DeletionCode_GeneratingEnumeration_exists_ordered_enumeration
import Theorems.Thm_DeletionCode_GeneratingEnumeration_CataloguePresentation_signedGenerating

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingEnumeration
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph SupportComponents
open CanonicalIndex ConnectedBlocks FiniteGenerating
open scoped BigOperators
namespace DeletionCode.GeneratingEnumeration
theorem _root_.solution {t k n : ℕ} (x : Letters) (G : RuleSet k)
    (hgen : GeneratingAt (wordSpectrum x n (windowLength k)) G)
    (hcat : ∀ w ∈ G, CatalogueRule t k w) :
    ManuscriptCounting.GeneratingSet t x n k G.card (componentCount G) G := by
  classical
  obtain ⟨e, horder⟩ := exists_ordered_enumeration (wordSpectrum x n (windowLength k)) G hgen
  let rules : Fin G.card → Gram (windowLength k) → ℤ := fun r => (e r).val
  let P := presentationOfCatalogue rules (fun r => hcat (e r).val (e r).property)
  have himage : Finset.univ.image rules = G := by
    ext u
    constructor
    · intro hu
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hu
      exact (e r).property
    · intro hu
      obtain ⟨r, hr⟩ := e.surjective ⟨u, hu⟩
      exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, congrArg Subtype.val hr⟩
  have hrules : rulesOfFamily (flatFamily t G.card P.words) (group t G.card) = G := by
    calc
      rulesOfFamily (flatFamily t G.card P.words) (group t G.card) = Finset.univ.image rules := by
        unfold rulesOfFamily
        apply Finset.image_congr
        intro r hr
        exact P.rule_eq r
      _ = G := himage
  exact ⟨rfl, rfl, P.words, P.valid, P.balanced,
    P.signedGenerating x n horder, hrules⟩
end DeletionCode.GeneratingEnumeration
