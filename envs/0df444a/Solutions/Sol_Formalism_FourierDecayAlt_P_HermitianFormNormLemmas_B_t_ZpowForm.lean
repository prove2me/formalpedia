-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.t_ZpowForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:13.861309+00:00
-- url     : https://prove2.me/submissions/3dc2ca06-cbc3-4410-a3b7-25d84eb4db57

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
theorem _root_.solution : Formalism.FourierDecayAlt.PN.ZpowForm := by
  unfold Formalism.FourierDecayAlt.PN.ZpowForm
  intro q k r _ hk
  rw [zpow_neg]
  congr 1
  have e : ((k : ℤ) - 2 * r - 5) = ((k - 2 * r - 5 : ℕ) : ℤ) := by omega
  rw [e, zpow_natCast]
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
