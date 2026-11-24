-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.polar_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:40:58.94205+00:00
-- url     : https://prove2.me/submissions/a0efea02-4741-44bc-8734-7fc569808c71

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_lintegral_normSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (h0 : ∀ s ≤ 0, φ s = 0) :
    ∫⁻ z : ℂ, φ (Complex.normSq z - 1) = ∫⁻ z : ℂ, φ (Complex.normSq z) := by
  rw [lintegral_normSq (fun s => φ (s - 1)) (hφ.comp (measurable_id.sub_const 1)), lintegral_normSq φ hφ]
  congr 1
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
  rw [← lintegral_add_right_eq_self _ (1 : ℝ)]
  refine lintegral_congr fun s => ?_
  by_cases hs : 0 < s
  · have h1 : s + 1 ∈ Set.Ioi (0 : ℝ) := by show (0 : ℝ) < s + 1; linarith
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show s ∈ Set.Ioi (0 : ℝ) from hs)]
    simp
  · rw [Set.indicator_of_notMem (show s ∉ Set.Ioi (0 : ℝ) from hs)]
    by_cases h1 : s + 1 ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem h1]
      simpa using h0 s (not_lt.1 hs)
    · rw [Set.indicator_of_notMem h1]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
