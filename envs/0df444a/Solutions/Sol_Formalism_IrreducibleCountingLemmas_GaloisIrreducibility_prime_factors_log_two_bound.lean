-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.prime_factors_log_two_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:25:10.189244+00:00
-- url     : https://prove2.me/submissions/9a2ab978-0057-4f50-94eb-0ae5e8f56c25

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
theorem _root_.solution : PrimeFactorsLogTwo := by
  intro g δ hg hδ
  have hgδ : 2 ≤ g ^ δ := le_trans hg (Nat.le_self_pow (by omega) g)
  have h1 : 2 ^ (g ^ δ - 1).primeFactors.card ≤ g ^ δ - 1 := by
    calc 2 ^ (g ^ δ - 1).primeFactors.card ≤ ∏ p ∈ (g ^ δ - 1).primeFactors, p :=
          Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ g ^ δ - 1 := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd _)
  have key : (2 : ℝ) ^ (g ^ δ - 1).primeFactors.card ≤ (g : ℝ) ^ δ := by
    have h2 : 2 ^ (g ^ δ - 1).primeFactors.card ≤ g ^ δ := by omega
    exact_mod_cast h2
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  rw [← Real.logb_pow, Real.le_logb_iff_rpow_le (by norm_num) (pow_pos hg0 _), Real.rpow_natCast]
  exact key
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
