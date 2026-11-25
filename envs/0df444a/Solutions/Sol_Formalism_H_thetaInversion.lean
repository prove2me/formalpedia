-- Prove2me | solution 1 for Formalism.H.thetaInversion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:58:37.517812+00:00
-- url     : https://prove2.me/submissions/7b801722-dc6d-4b9e-b622-34a10cf3a41e

import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Assembly
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Periodization
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_UnfoldCoeff
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeFourierSeries
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_DualLattice
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_CovolumeDual
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Theorems.Thm_Formalism_H_thetaShiftInversion
import Theorems.Thm_Formalism_H_thetaInversion_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.H
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable [MeasurableSpace V] [BorelSpace V]
namespace Formalism.H
theorem _root_.solution : ThetaInversion V := thetaInversion_of (thetaShiftInversion V)
end Formalism.H
