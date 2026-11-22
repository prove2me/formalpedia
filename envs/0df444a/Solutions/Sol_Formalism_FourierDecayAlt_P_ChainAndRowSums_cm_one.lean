-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChainAndRowSums.cm_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:40.380798+00:00
-- url     : https://prove2.me/submissions/537ef3b4-eb62-4e44-9dc4-9fe56833b898

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainAndRowSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChainAndRowSums
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.ChainAndRowSums
theorem _root_.solution {W : Type} (Wd : Finset W) (c : ℕ → W → W → ℝ) : chainMat Wd c 1 = c 1 := by
  simp [chainMat]
end Formalism.FourierDecayAlt.P.ChainAndRowSums
