-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.exact_coefficient_difference
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:30:37.567434+00:00
-- url     : https://prove2.me/submissions/4fadeccf-6db3-404d-a297-e9eb0c81ab53

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer
namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
theorem _root_.solution : ExactCoeffDiff := by
  intro U0 W Top m f D bN hW u0
  obtain ⟨hf, hm1, hmk, hmx, hL, hv, hl0, hl1, hl2, hlg, hb⟩ := hW
  have hf0 : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hk0 : 0 < D.k := by linarith
  have hvp : 0 < D.v / π := div_pos hv Real.pi_pos
  have h1 : ∀ j ρ, Real.log (D.w u0 j ρ * D.v / π) = Real.log (D.w u0 j ρ) + Real.log (D.v / π) := by
    intro j ρ
    rw [mul_div_assoc, Real.log_mul (hb u0 j ρ).2.1.ne' hvp.ne']
  have h2 : (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π))
      = (1 / (f : ℝ)) * (∑ ρ : Fin f, ∑ j : Fin m, Real.log (D.w u0 j ρ)) + (m : ℝ) * Real.log (D.v / π) := by
    simp_rw [h1]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have h3 : (∑ ρ : Fin f, ∑ j : Fin m, (Real.log (D.w u0 j ρ) - Real.log (bN u0 j ρ)))
      = (∑ ρ : Fin f, ∑ j : Fin m, Real.log (D.w u0 j ρ))
        - ∑ ρ : Fin f, ∑ j : Fin m, Real.log (bN u0 j ρ) := by
    simp only [Finset.sum_sub_distrib]
  unfold mainCount exactMain
  rw [h2, h3]
  field_simp
  ring
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
