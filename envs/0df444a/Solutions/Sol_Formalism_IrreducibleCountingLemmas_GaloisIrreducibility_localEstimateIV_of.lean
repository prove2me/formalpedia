-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.localEstimateIV_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:36.81764+00:00
-- url     : https://prove2.me/submissions/5b558f29-b7af-4c97-a7a7-1b6aeea53236

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropositionOneCentralCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Theorems.Thm_P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic__60d833550372

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial Formalism.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (h : TypeSetWeight) (hP : LemmaPSubSum) (hD : DivisorDegreeSubSum) :
    LocalEstimateIV := by
  intro K _ _ N a ha haN
  classical
  have hfilt : (sqSet K N).filter (fun c => ∃ h : K[X], h ∣ monicOf c ∧ h.natDegree = a) =
      (sqSet K N).filter (fun c => IsSubSum (degType (monicOf c)) a) := by
    apply Finset.filter_congr
    intro c _
    exact hD K (monicOf c) a (monicOf_monic' c).ne_zero
  rw [hfilt]
  refine le_trans (h K N (fun m => IsSubSum m a)) ?_
  have hP' := hP N a ha haN
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [div_le_iff₀ hf]
  have h8 : (8 : ℝ) * (((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun σ => IsSubSum σ.partition.parts a)).card : ℝ) ≤ 7 * N.factorial := by
    exact_mod_cast hP'
  linarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
