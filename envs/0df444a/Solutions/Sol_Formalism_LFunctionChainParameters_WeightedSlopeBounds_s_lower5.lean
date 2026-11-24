-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.WeightedSlopeBounds.s_lower5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:28:55.639912+00:00
-- url     : https://prove2.me/submissions/da2a5726-c4cd-490b-a612-0f62a4bf9de8

import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_exponent_le_upper
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_Data_sumA_nonneg
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_Data_sum_aT_mul
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_sub_wmean_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.RankGapBounds.WeightedMeanData
noncomputable section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
namespace Formalism.LFunctionChainParameters.WeightedSlopeBounds
theorem _root_.solution (hS : D.HidaSetting C) (hDIV : D.DIV C) (hE : EComp5 D C) (hCount : Count5 D C)
    (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp) (u0 : U0) :
    D.Ga u0 + D.muCC u0 - K5v5 D C u0 - wmean (D.d u0) (Lo5 D C Xpp u0) ≤ D.s u0 := by
  have hA := D.sumA_nonneg C hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hd, -⟩ := hS
  unfold Data.s
  refine sub_wmean_le (hd u0) _ (fun u => ?_)
  have h1 := (hSN u0 u).2
  have h2 := hDIV u0 u
  rw [Finset.sum_sub_distrib, Data.sum_aT_mul] at h2
  have h3 : Lam5 D C u0 ≤ Real.log (D.T u0 u) := (hCount u0 u).1
  have h4 := mul_le_mul_of_nonneg_left h3 hA
  have h5 := exponent_le_upper D C hE u0 u
  have h6 := (hSl u0 u).1
  unfold K5v5 Data.SDiv Data.EDiv
  try dsimp only
  linarith
end Formalism.LFunctionChainParameters.WeightedSlopeBounds
