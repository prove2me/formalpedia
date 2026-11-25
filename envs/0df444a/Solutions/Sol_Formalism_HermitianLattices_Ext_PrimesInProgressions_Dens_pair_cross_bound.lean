-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.pair_cross_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:31:04.129816+00:00
-- url     : https://prove2.me/submissions/b6a7a90c-b227-467f-a7ad-583b324b8509

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_norm_sum_twist_le
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_character_sum_range_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution : PairCross := by
  intro M _ ψ hψ w hw U hU
  have h := norm_sum_twist_le (fun n => ψ (n : ZMod M)) (m := (M : ℝ))
    (fun k => norm_character_sum_range_le ψ hψ k) hw hU
  refine h.trans ?_
  have : (0 : ℝ) ≤ M := by positivity
  nlinarith [norm_nonneg w]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
