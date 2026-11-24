-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.divisor_degree_subsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:51:02.760661+00:00
-- url     : https://prove2.me/submissions/306856e9-84bc-4891-b442-c0a66a4f1d75

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Lemmata_GeneralBFactRightRest_Imports
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_exists_le_map_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial UniqueFactorizationMonoid
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.GaloisIrreducibility (IsSubSum)
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : DivisorDegreeSubSum := by
  classical
  intro K _ f a hf
  have hdeg : ∀ t : Multiset K[X], t ≤ normalizedFactors f →
      t.prod.natDegree = (t.map natDegree).sum := by
    intro t ht
    apply natDegree_multiset_prod
    intro h0
    exact zero_notMem_normalizedFactors f (Multiset.mem_of_le ht h0)
  constructor
  · rintro ⟨h, hdvd, rfl⟩
    have hh : h ≠ 0 := fun h0 => hf (by rw [h0] at hdvd; exact zero_dvd_iff.mp hdvd)
    have hle : normalizedFactors h ≤ normalizedFactors f :=
      (dvd_iff_normalizedFactors_le_normalizedFactors hh hf).mp hdvd
    refine ⟨(normalizedFactors h).map natDegree, Multiset.map_le_map hle, ?_⟩
    rw [← hdeg _ hle]
    exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (prod_normalizedFactors hh))
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨u, hu, rfl⟩ := exists_le_map_eq natDegree _ s hs
    refine ⟨u.prod, ?_, hdeg u hu⟩
    exact (Multiset.prod_dvd_prod_of_le hu).trans (prod_normalizedFactors hf).dvd
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
