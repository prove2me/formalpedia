-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:20.144661+00:00
-- url     : https://prove2.me/submissions/592b3943-6b3d-4f80-a9ae-76154b4b7c8e

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
theorem _root_.solution (K : ℕ) {L : ℝ} (hL : 0 ≤ L) (a : ℝ) (ha : 0 ≤ a) : 0 ≤ mfac K L a := by
  unfold mfac
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (by positivity)
end Formalism.FourierDecayAlt.P.LatticeSummability
