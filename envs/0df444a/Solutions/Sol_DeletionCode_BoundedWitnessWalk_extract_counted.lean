-- Prove2me | solution 1 for DeletionCode.BoundedWitnessWalk.extract_counted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:00:44.964973+00:00
-- url     : https://prove2.me/submissions/e882aeda-0cf1-4b76-a231-2e3355008d26

import Definitions.Def_DeletionCode_WitnessCases
import Definitions.Def_DeletionCode_FiniteWalkRules
import Definitions.Def_DeletionCode_GeneratingEnumeration
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_BoundedWitnessWalk
import Theorems.Thm_DeletionCode_BoundedWitnessWalk_extract
import Theorems.Thm_DeletionCode_GeneratingEnumeration_generatingAt_to_manuscript
import Theorems.Thm_DeletionCode_WalkSelection_ScanState_generating


set_option autoImplicit true
open DeletionCode DeletionCode.BoundedWitnessWalk
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open CatalogueAlgebra FiniteWalkRules WalkSelection BlockPartition WitnessCases
namespace DeletionCode.BoundedWitnessWalk
theorem _root_.solution {t k m n : ℕ} (ht : 2 ≤ t) (x : Letters)
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ)
    (K : Set (Gram (windowLength k) → ℤ))
    (hbase : p 0 = wordSpectrum x n (windowLength k))
    (hp : ∀ j, WitnessAlgebra.BooleanVector (rationalPath p j))
    (hclosed : p 0 = p (Fin.last m)) (hodd : Odd m)
    (hcat : ∀ i, CatalogueRule t k (step p i))
    (hK : ∀ i, step p i ∈ K) :
    ∃ U : RuleSet k, Witness t k (wordSpectrum x n (windowLength k)) K U ∧
      ManuscriptCounting.GeneratingSet t x n k U.card (componentCount U) U := by
  obtain ⟨U, hU⟩ := extract ht p K hp hclosed hodd hcat hK
  rw [hbase] at hU
  exact ⟨U, hU, GeneratingEnumeration.generatingAt_to_manuscript x U
    hU.generating hU.catalogue⟩
end DeletionCode.BoundedWitnessWalk
