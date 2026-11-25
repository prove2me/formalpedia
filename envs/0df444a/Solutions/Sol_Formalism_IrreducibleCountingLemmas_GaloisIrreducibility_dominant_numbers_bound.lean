-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.dominant_numbers_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:08:11.626372+00:00
-- url     : https://prove2.me/submissions/24d6b90f-2dad-4172-a1f2-21c8ed625e13

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
open Filter Topology
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : NumbersDominant := by
  intro C ε hε
  have hε0 : ε ≠ 0 := hε.ne'
  have ha : 0 < ε / 6 := by positivity
  have hab : 0 < ε / 6 - ε / 7 := by linarith
  have hA : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x ^ (ε / 6 - ε / 7) :=
    (tendsto_rpow_atTop hab).eventually_ge_atTop 2
  have hB : ∀ᶠ x : ℝ in Filter.atTop,
      (x ^ (ε / 6)) ^ (C / (ε / 6)) * Real.exp (-(1 / 2) * x ^ (ε / 6)) < 1 / 8 := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (C / (ε / 6)) (1 / 2)
      (by norm_num)).comp (tendsto_rpow_atTop ha)
    exact h.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hA, hB, Filter.eventually_gt_atTop 0] with x hxA hxB hx0
  have hxa : x ^ (ε / 6) = x ^ (ε / 6 - ε / 7) * x ^ (ε / 7) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have hpow : (x ^ (ε / 6)) ^ (C / (ε / 6)) = x ^ C := by
    rw [← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  have hxb0 : 0 < x ^ (ε / 7) := Real.rpow_pos_of_pos hx0 _
  have hle : x ^ (ε / 7) ≤ x ^ (ε / 6) / 2 := by
    rw [hxa]
    nlinarith
  rw [hpow] at hxB
  calc x ^ C * Real.exp (-x ^ (ε / 6))
      = x ^ C * Real.exp (-(1 / 2) * x ^ (ε / 6)) * Real.exp (-(1 / 2) * x ^ (ε / 6)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
    _ ≤ 1 / 8 * Real.exp (-(1 / 2) * x ^ (ε / 6)) :=
        mul_le_mul_of_nonneg_right hxB.le (Real.exp_pos _).le
    _ ≤ 1 / 8 * Real.exp (-x ^ (ε / 7)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.exp_le_exp.mpr (by linarith)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
