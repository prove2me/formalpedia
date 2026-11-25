-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.not_mem_bad_primes_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:07:06.2717+00:00
-- url     : https://prove2.me/submissions/5581afe0-5388-4a10-860b-323947ed2c8f

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
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_BB_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open scoped ComplexOrder
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : NotMemBBIff := by
  intro g N l hg hl hlg
  rw [mem_BB_iff]
  constructor
  · intro h d hd
    by_contra hc
    push_neg at hc
    apply h
    right
    refine ⟨?_, hl, d, hd, hc⟩
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
    have hgd : 2 ≤ g ^ d := le_trans hg (Nat.le_self_pow (by omega) g)
    rcases Nat.eq_zero_or_pos (padicValNat l (g ^ d - 1)) with h0 | h0
    · rw [h0, mul_zero, pow_zero] at hc
      omega
    have hdvd : l ∣ g ^ d - 1 := dvd_of_one_le_padicValNat h0
    have hle : l ≤ g ^ d - 1 := Nat.le_of_dvd (by omega) hdvd
    have hpow : g ^ d ≤ g ^ N := Nat.pow_le_pow_right (by omega) hdN
    omega
  · rintro h (rfl | ⟨-, -, d, hd, hlt⟩)
    · exact hlg rfl
    · exact absurd (h d hd) (not_le.mpr hlt)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
