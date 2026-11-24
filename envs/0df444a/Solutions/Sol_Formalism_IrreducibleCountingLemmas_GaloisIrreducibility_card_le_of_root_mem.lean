-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_le_of_root_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:29.642799+00:00
-- url     : https://prove2.me/submissions/d830b990-2ff7-465d-befb-6668031ca57b

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRFrobOrbitIrred
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSamePartCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_eq_of_common_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {δ : ℕ} (F : Finset (Fin δ → K))
    (hF : ∀ c ∈ F, Irreducible (monicOf c)) (S : Finset L)
    (h : ∀ c ∈ F, ∃ x ∈ S, aeval x (monicOf c) = 0) : F.card ≤ S.card := by
  classical
  choose! r hrS hr using h
  refine Finset.card_le_card_of_injOn r (fun c hc => hrS c hc) ?_
  intro a ha b hb hab
  exact eq_of_common_root (hF a ha) (hF b hb) (hr a ha) (hab ▸ hr b hb)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
