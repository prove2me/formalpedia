-- Prove2me | solution 1 for DeletionCode.WordGraphWitness.finite_word_component_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:08:21.06793+00:00
-- url     : https://prove2.me/submissions/9e5d5778-fb05-46b7-8561-71b2a0671c60

import Definitions.Def_DeletionCode_OddGraphWalk
import Definitions.Def_DeletionCode_BoundedWitnessWalk
import Definitions.Def_DeletionCode_WordGraphWitness
import Theorems.Thm_DeletionCode_WordGraphWitness_component_witness

set_option autoImplicit true
open DeletionCode DeletionCode.WordGraphWitness
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open ConnectedBlocks WitnessCases
namespace DeletionCode.WordGraphWitness
theorem _root_.solution {t k n : ℕ} (ht : 2 ≤ t)
    (vertices : Set (Bits n)) (G : SimpleGraph vertices)
    (K : Set (Gram (windowLength k) → ℤ))
    (hunique : ∀ v ∈ vertices, KUnique (padBits v) n k)
    (hcat : ∀ {v w}, G.Adj v w → CatalogueRule t k
      (wordSpectrum (padBits w.val) n (windowLength k) -
        wordSpectrum (padBits v.val) n (windowLength k)))
    (hK : ∀ {v w}, G.Adj v w →
      (wordSpectrum (padBits w.val) n (windowLength k) -
        wordSpectrum (padBits v.val) n (windowLength k)) ∈ K)
    (x : vertices) (hnot : ¬ (G.connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet k,
      Witness t k (wordSpectrum (padBits x.val) n (windowLength k)) K U ∧
      ManuscriptCounting.GeneratingSet t (padBits x.val) n k U.card (componentCount U) U :=
  component_witness ht G (fun v => padBits v.val) K
    (fun v => hunique v.val v.property) hcat hK x hnot
end DeletionCode.WordGraphWitness
