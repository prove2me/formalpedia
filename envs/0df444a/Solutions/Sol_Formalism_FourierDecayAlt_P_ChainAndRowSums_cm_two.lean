-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChainAndRowSums.cm_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:42.688786+00:00
-- url     : https://prove2.me/submissions/ddc9c005-de70-4934-9bcc-f3d5498bae2b

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
theorem _root_.solution {W : Type} (Wd : Finset W) (c : ℕ → W → W → ℝ) (k : ℕ) (w w'' : W) :
    chainMat Wd c (k + 2) w w'' = ∑ w' ∈ Wd, c (k + 2) w w' * chainMat Wd c (k + 1) w' w'' := by
  simp [chainMat]
end Formalism.FourierDecayAlt.P.ChainAndRowSums
