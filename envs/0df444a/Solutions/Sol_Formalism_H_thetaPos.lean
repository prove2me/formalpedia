-- Prove2me | solution 1 for Formalism.H.thetaPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:58:53.076784+00:00
-- url     : https://prove2.me/submissions/64d4ce42-22c1-4f3e-8de0-dad5df1e3f94

import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Assembly
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Periodization
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_UnfoldCoeff
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_LatticeFourierSeries
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_DualLattice
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_CovolumeDual
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Theorems.Thm_Formalism_H_thetaSummable
import Theorems.Thm_Formalism_H_thetaPos_of


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
namespace Formalism.H
theorem _root_.solution : ThetaPos V := by
  let _ : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  exact thetaPos_of (thetaSummable V)
end Formalism.H
