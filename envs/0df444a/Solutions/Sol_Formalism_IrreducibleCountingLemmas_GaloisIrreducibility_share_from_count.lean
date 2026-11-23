-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.share_from_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:57.163062+00:00
-- url     : https://prove2.me/submissions/c5b80b6c-7573-422e-afe7-924bda059c26

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
theorem _root_.solution : ShareFromCount := by
  intro ε W₁ W₂ PP₁ PP₂ D₁ D₂ Dall Dstar bad hε0 hε1 hD hP1 hPW1 hP2 hPW2 hall h1 h2 hbad
  have hall' : (1 - ε) * Dstar ≤ Dall := by
    have := (abs_le.mp hall).1
    linarith
  have h1e : 0 < 1 - ε := by linarith
  have hDall : 0 < Dall := lt_of_lt_of_le (mul_pos h1e hD) hall'
  have hd1 : D₁ ≤ (1 + ε) * W₁ * Dstar := by
    have := (abs_le.mp h1).2
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) hD.le) (sub_nonneg.mpr hPW1)]
  have hd2 : D₂ ≤ (1 + ε) * W₂ * Dstar := by
    have := (abs_le.mp h2).2
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + ε) hD.le) (sub_nonneg.mpr hPW2)]
  have hW : 0 ≤ W₁ + W₂ := by linarith
  have hne : 1 - ε ≠ 0 := h1e.ne'
  have hc : 0 ≤ (1 + ε) / (1 - ε) * (W₁ + W₂) :=
    mul_nonneg (div_nonneg (by linarith) h1e.le) hW
  rw [div_le_iff₀ hDall]
  calc bad ≤ (1 + ε) * (W₁ + W₂) * Dstar := by linarith
    _ = (1 + ε) / (1 - ε) * (W₁ + W₂) * ((1 - ε) * Dstar) := by
        rw [show (1 + ε) / (1 - ε) * (W₁ + W₂) * ((1 - ε) * Dstar)
            = (1 + ε) * (W₁ + W₂) * Dstar * ((1 - ε) / (1 - ε)) by ring, div_self hne, mul_one]
    _ ≤ (1 + ε) / (1 - ε) * (W₁ + W₂) * Dall := mul_le_mul_of_nonneg_left hall' hc
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
