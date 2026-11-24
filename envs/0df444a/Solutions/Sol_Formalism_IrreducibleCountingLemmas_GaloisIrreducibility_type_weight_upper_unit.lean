-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.type_weight_upper_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:03.845064+00:00
-- url     : https://prove2.me/submissions/bc2be943-e950-4e24-8ab1-d2a06473de1e

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
theorem _root_.solution : TypeWeightU := by
  intro g D Nd n hg hD hN
  rw [one_div, ← Finset.prod_inv_distrib]
  apply Finset.prod_le_prod
  · intro d hd
    have hgd : (1 : ℝ) ≤ (g : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ g))
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)
  · intro d hd
    have hd1 := hD d hd
    have hgd : (1 : ℝ) < (g : ℝ) ^ d := one_lt_pow₀ (by exact_mod_cast (by omega : 1 < g)) (by omega)
    have hNd : (d : ℝ) * (Nd d : ℝ) ≤ (g : ℝ) ^ d - 1 := by
      have h := hN d hd
      have h1 : 1 ≤ g ^ d := Nat.one_le_pow _ _ (by omega)
      have h2 : ((d * Nd d : ℕ) : ℝ) ≤ ((g ^ d - 1 : ℕ) : ℝ) := by exact_mod_cast h
      rw [Nat.cast_sub h1] at h2
      push_cast at h2
      linarith
    have hpos : (0 : ℝ) < (g : ℝ) ^ d - 1 := by linarith
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hfact : (0 : ℝ) < ((n d).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    calc ((Nd d).choose (n d) : ℝ) / ((g : ℝ) ^ d - 1) ^ (n d)
        ≤ ((Nd d : ℝ) ^ (n d) / ((n d).factorial : ℝ)) / ((g : ℝ) ^ d - 1) ^ (n d) :=
          div_le_div_of_nonneg_right (Nat.choose_le_pow_div _ _) (pow_nonneg hpos.le _)
      _ ≤ ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ))⁻¹ := by
          rw [div_div, inv_eq_one_div, div_le_div_iff₀ (mul_pos hfact (pow_pos hpos _))
            (mul_pos (pow_pos hdpos _) hfact), one_mul]
          have hp : ((d : ℝ) * Nd d) ^ (n d) ≤ ((g : ℝ) ^ d - 1) ^ (n d) :=
            pow_le_pow_left₀ (by positivity) hNd _
          calc (Nd d : ℝ) ^ (n d) * ((d : ℝ) ^ (n d) * ((n d).factorial : ℝ))
              = ((d : ℝ) * Nd d) ^ (n d) * ((n d).factorial : ℝ) := by ring
            _ ≤ ((g : ℝ) ^ d - 1) ^ (n d) * ((n d).factorial : ℝ) :=
                mul_le_mul_of_nonneg_right hp hfact.le
            _ = ((n d).factorial : ℝ) * ((g : ℝ) ^ d - 1) ^ (n d) := by ring
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
