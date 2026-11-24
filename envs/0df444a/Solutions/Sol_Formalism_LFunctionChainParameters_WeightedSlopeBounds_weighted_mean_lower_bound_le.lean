-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.WeightedSlopeBounds.weighted_mean_lower_bound_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:12:01.580142+00:00
-- url     : https://prove2.me/submissions/6b62a642-9c04-4561-9e72-c9cfc74da36d

import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_Data_nT_nonneg
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_wmean_le_const


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
theorem _root_.solution (hS : D.HidaSetting C) (hCount : Count5 D C) (u0 : U0) :
    wmean (D.d u0) (Lo5 D C Xpp u0) ≤ C.cSl1 * D.IO u0 + K7v5 D C Xpp := by
  obtain ⟨-, -, ha, hb', hk, -, -, -, -, hd, -, -, hcSl1, -⟩ := hS
  refine wmean_le_const (hd u0) _ (fun u => ?_)
  have hc : 0 ≤ C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') :=
    mul_nonneg (mul_nonneg (mul_nonneg hcSl1 D.nT_nonneg) (Nat.cast_nonneg _))
      (add_nonneg (div_nonneg ha hk.le) hb')
  have h1 := mul_le_mul_of_nonneg_left (hCount u0 u).2.1 hc
  unfold Lo5 K7v5
  linarith
end Formalism.LFunctionChainParameters.WeightedSlopeBounds
