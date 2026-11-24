-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.excluded_set_simplification
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:29.826592+00:00
-- url     : https://prove2.me/submissions/aa7e3248-5846-4dfd-b1b3-b45ffb8a84db

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

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : ExcludedSimplify := by
  intro N Y hN hY
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 1 ≤ Y ^ ((3 : ℝ) / 4) := Real.one_le_rpow hY (by norm_num)
  generalize Y ^ ((3 : ℝ) / 4) = t at ht ⊢
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have h1 : (3 * N + 1 : ℝ) ≤ 4 * N := by linarith
  have h2 : 1 + 2 * (N : ℝ) ^ 2 * (t + 1) ≤ 5 * (N : ℝ) ^ 2 * t := by nlinarith
  calc (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (t + 1)) ≤ (4 * N) * (5 * (N : ℝ) ^ 2 * t) :=
        mul_le_mul h1 h2 (by nlinarith) (by linarith)
    _ = 20 * (N : ℝ) ^ 3 * t := by ring
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
