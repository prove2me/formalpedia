-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.top_from_weighted_mean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:30:38.830827+00:00
-- url     : https://prove2.me/submissions/01da74e0-a1fb-43df-a58e-00cbe0ac82f6

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
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds
theorem _root_.solution {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] : LeadingTermTranslateMean (H := H) := by
  intro W _ _ Top _ m f Dd D N ell TT a w eT eP E haT hw hgam hLpL hASK hle
  have hH : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hfc : f = (PhiSet (H := H)).card := by
    have := Fintype.card_congr eP
    simpa using this
  have hMain : ∀ u0, Dd.Main u0 = ∑ t ∈ TT, ∑ j : Fin m, (MAIN ell (a t) (w u0 j)).re := by
    intro u0
    unfold Formalism.RankGapBounds.WeightedMeanData.Data.Main
    rw [Finset.sum_comm]
    have hre : ∀ (t : H) (j : Fin m), (MAIN ell (a t) (w u0 j)).re
        = a t * (Real.log (a t) - 1 - Real.eulerMascheroniConstant + (ell chC).re
          - (1 / ((PhiSet (H := H)).card : ℝ)) * ∑ ρ ∈ PhiSet (H := H), Real.log (w u0 j ρ)) := by
      intro t j
      unfold MAIN
      rw [Complex.re_ofReal_mul, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_re]
    simp only [hre]
    rw [← Finset.sum_coe_sort TT, ← Equiv.sum_comp eT]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun j _ => ?_
    have hfR : (f : ℝ) = ((PhiSet (H := H)).card : ℝ) := by exact_mod_cast hfc
    have hsum : ∑ ρ : Fin f, Real.log (Dd.w u0 j ρ) = ∑ ρ ∈ PhiSet (H := H), Real.log (w u0 j ρ) := by
      rw [← Finset.sum_coe_sort (PhiSet (H := H)), ← Equiv.sum_comp eP]
      exact Finset.sum_congr rfl fun ρ _ => by rw [hw]
    rw [haT, hgam, hLpL, hfR, hsum]
  unfold topExcess
  unfold Formalism.RankGapBounds.WeightedMeanData.umean at hle
  simp only [hASK, hMain] at hle
  simp only [Finset.sum_sub_distrib]
  rw [mul_sub, one_div, inv_mul_eq_div, inv_mul_eq_div]
  linarith
end Formalism.LFunctionChainParameters.ThickSetMeanBounds
