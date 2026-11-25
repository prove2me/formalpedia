-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.admissible_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:12:32.910342+00:00
-- url     : https://prove2.me/submissions/950a5436-3f5e-4db7-8e1a-de6499e9f53d

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
theorem _root_.solution : AdmissibleCount := by
  intro c₀ c X B h P A hc₀ hc hX hlog hB hBc hh hhc hP hPA
  have hlogpos : 0 < Real.log X := Real.log_pos hX
  have hcpos : 0 < c := lt_of_lt_of_le hlogpos hlog
  have hX0 : 0 < X := by linarith
  have hc0c : (2 : ℝ) ^ 14 ≤ c₀ * c := by
    rw [div_le_iff₀ hc₀] at hc
    linarith
  have hB5 : B ^ 5 ≤ 1024 * c ^ 15 := by
    calc B ^ 5 ≤ (4 * c ^ 3) ^ 5 := pow_le_pow_left₀ hB.le hBc 5
      _ = 1024 * c ^ 15 := by ring
  have hden : h * Real.log X ≤ c ^ 4 := by
    calc h * Real.log X ≤ c ^ 3 * c := mul_le_mul hhc hlog hlogpos.le (pow_pos hcpos 3).le
      _ = c ^ 4 := by ring
  have hB0 : 0 < B ^ 5 := pow_pos hB 5
  have hD0 : 0 < h * Real.log X := mul_pos hh hlogpos
  have hP' : c₀ * X / (1024 * c ^ 19) ≤ P := by
    refine le_trans ?_ hP
    have e : c₀ * B ^ (-5 : ℤ) * X / (h * Real.log X) = c₀ * X / (B ^ 5 * (h * Real.log X)) := by
      rw [zpow_neg, zpow_ofNat]
      field_simp
    rw [e, div_le_div_iff₀ (mul_pos (by norm_num) (pow_pos hcpos 19)) (mul_pos hB0 hD0)]
    have h1 : B ^ 5 * (h * Real.log X) ≤ 1024 * c ^ 19 := by
      calc B ^ 5 * (h * Real.log X) ≤ (1024 * c ^ 15) * c ^ 4 :=
            mul_le_mul hB5 hden hD0.le (mul_pos (by norm_num) (pow_pos hcpos 15)).le
        _ = 1024 * c ^ 19 := by ring
    exact mul_le_mul_of_nonneg_left h1 (mul_pos hc₀ hX0).le
  have hA : 8 * c ^ (-20 : ℤ) * X ≤ c₀ * X / (2048 * c ^ 19) := by
    have e : 8 * c ^ (-20 : ℤ) * X = 8 * X / c ^ 20 := by
      rw [zpow_neg, zpow_ofNat]
      ring
    rw [e, div_le_div_iff₀ (pow_pos hcpos 20) (mul_pos (by norm_num) (pow_pos hcpos 19))]
    nlinarith [mul_nonneg (mul_pos hX0 (pow_pos hcpos 19)).le (sub_nonneg.mpr hc0c)]
  have e2 : c₀ * X / (2048 * c ^ 19) = (c₀ * X / (1024 * c ^ 19)) / 2 := by ring
  calc 8 * c ^ (-20 : ℤ) * X ≤ c₀ * X / (2048 * c ^ 19) := hA
    _ = (c₀ * X / (1024 * c ^ 19)) / 2 := e2
    _ ≤ P / 2 := by linarith
    _ ≤ A := by linarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
