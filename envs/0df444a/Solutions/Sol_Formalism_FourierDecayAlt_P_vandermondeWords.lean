-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.vandermondeWords
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:51.268866+00:00
-- url     : https://prove2.me/submissions/74ba2661-dd5c-4d5b-a068-4b2a14a3a990

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.VandWords := by
  intro c de de' hc hv hw hw'
  obtain ⟨hpos, hle⟩ := vand_le c de de' hc hv hw hw'
  obtain ⟨hpos', hle'⟩ := vand_le c de' de hc hv hw' hw
  refine ⟨hpos, hpos', ?_⟩
  rw [abs_le]
  constructor
  · rw [Real.le_log_iff_exp_le (div_pos hpos' hpos), le_div_iff₀ hpos, Real.exp_neg,
      inv_mul_le_iff₀ (Real.exp_pos _)]
    exact hle'
  · rw [Real.log_le_iff_le_exp (div_pos hpos' hpos), div_le_iff₀ hpos]
    exact hle
end Formalism.FourierDecayAlt.P
