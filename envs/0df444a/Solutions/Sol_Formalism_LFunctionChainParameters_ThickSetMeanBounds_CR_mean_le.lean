-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR.mean_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:50.67626+00:00
-- url     : https://prove2.me/submissions/ba803952-96f9-4f10-a8eb-57c445e8a520

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
open Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR
theorem _root_.solution {m : ℕ} (TT : Finset H) (F G : H → H → Fin m → ℝ) (K : ℝ)
    (h : ∀ u0, ∀ t ∈ TT, ∀ j, F u0 t j ≤ G u0 t j + K) :
    (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, F u0 t j
      ≤ (1 / (Fintype.card H : ℝ)) * (∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, G u0 t j) + (TT.card : ℝ) * m * K := by
  have hH : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have h1 : ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, F u0 t j
      ≤ ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, (G u0 t j + K) :=
    Finset.sum_le_sum fun u0 _ => Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun j _ => h u0 t ht j
  have h2 : ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, (G u0 t j + K)
      = (∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, G u0 t j) + (Fintype.card H : ℝ) * ((TT.card : ℝ) * m * K) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    ring
  calc (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, F u0 t j
      ≤ (1 / (Fintype.card H : ℝ)) * ((∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m, G u0 t j)
          + (Fintype.card H : ℝ) * ((TT.card : ℝ) * m * K)) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by field_simp
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR
