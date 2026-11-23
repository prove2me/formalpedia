-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LatticeSummability.mfac_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:25.318805+00:00
-- url     : https://prove2.me/submissions/15dabaa2-4173-4b49-8f83-af34d75627b3

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Finset Function
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LatticeSummability
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.LatticeSummability
theorem _root_.solution (K : ℕ) {L : ℝ} (hL : 0 < L) {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') :
    mfac K L b' ≤ mfac K L b := by
  unfold mfac
  by_cases hb0 : b = 0
  · rw [if_pos hb0]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hb'0 : b' ≠ 0 := by linarith
    rw [if_neg hb0, if_neg hb'0]
    refine min_le_min le_rfl (pow_le_pow_left₀ (div_nonneg hL.le (by linarith)) ?_ K)
    exact div_le_div_of_nonneg_left hL.le hbpos hbb
end Formalism.FourierDecayAlt.P.LatticeSummability
