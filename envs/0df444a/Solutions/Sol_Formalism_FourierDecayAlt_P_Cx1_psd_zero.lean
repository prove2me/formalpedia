-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Cx1.psd_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:34:56.248639+00:00
-- url     : https://prove2.me/submissions/0281d240-c3ca-42dc-87b1-ca0efa41078a

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C
open scoped ComplexOrder
noncomputable section
open Classical
open Formalism.FourierDecayAlt.P.Cx1
namespace Formalism.FourierDecayAlt.P.Cx1
theorem _root_.solution {α : Type} (Y : Finset α) : TB.PSDOn Y (fun _ _ => (0 : ℂ)) := by
  simp only [TB.PSDOn]
  exact Matrix.PosSemidef.zero
end Formalism.FourierDecayAlt.P.Cx1
