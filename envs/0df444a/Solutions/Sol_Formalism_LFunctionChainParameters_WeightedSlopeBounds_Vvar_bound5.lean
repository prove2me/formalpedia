-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.WeightedSlopeBounds.Vvar_bound5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:45:33.801661+00:00
-- url     : https://prove2.me/submissions/b792e88f-39cf-49f6-a1e8-b72808fa7fc1

import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_exponent_le_upper
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_exponent_ge_lower
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_Data_sumA_nonneg
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_Data_sum_aT_mul


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
theorem _root_.solution (hS : D.HidaSetting C) (hE : EComp5 D C) (hH : D.HComp C) (hCount : Count5 D C)
    (u0 : U0) (u u' : W u0) :
    (-D.Ee u0 u - D.h u0 u) - (-D.Ee u0 u' - D.h u0 u') ≤ D.Vvar C := by
  have hA := D.sumA_nonneg C hS
  have h1 := exponent_le_upper D C hE u0 u'
  have h2 := exponent_ge_lower D C hE u0 u
  have h3 := (abs_le.mp (hH u0 u' u)).2
  rw [Data.sum_aT_mul, Data.sum_aT_mul] at h3
  have h4 := (abs_le.mp ((hCount u0 u).2.2 u')).2
  have h5 := mul_le_mul_of_nonneg_left h4 hA
  unfold Data.Vvar
  linarith
end Formalism.LFunctionChainParameters.WeightedSlopeBounds
